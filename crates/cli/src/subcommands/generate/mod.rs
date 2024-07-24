#![warn(clippy::uninlined_format_args)]

use std::fs;
use std::io::Write;
use std::ops::Deref;
use std::path::{Path, PathBuf};

use clap::{Arg, ArgAction, ArgGroup, ArgMatches};
use convert_case::{Case, Casing};
use duct::cmd;
use serde::de::IntoDeserializer;
use serde_json::Value;
use spacetimedb_lib::de::serde::DeserializeWrapper;
use spacetimedb::host::module_host::ModuleEvent;
use spacetimedb_lib::sats::{satn, AlgebraicType, Typespace};
use spacetimedb_lib::MODULE_ABI_MAJOR_VERSION;
use spacetimedb_lib::{bsatn, MiscModuleExport, ModuleDef, ReducerDef, TableDesc, TypeAlias, sats};
use wasmbin::Module;
use wasmtime::{AsContext, Caller};

use crate::common_args;
use crate::Config;
use crate::api::ClientApi;
use crate::sql::parse_req;

mod code_indenter;
pub mod csharp;
pub mod python;
pub mod rust;
pub mod typescript;
mod util;


const INDENT: &str = "\t";

pub fn cli() -> clap::Command {
    clap::Command::new("generate")
        .about("Generate client files for a spacetime module.")
        .arg(
            Arg::new("database")
                .required(true)
                .help("The domain or address of the database you would like to query"),
        )
        .arg(
            common_args::identity()
                .conflicts_with("anon_identity")
                .help("The identity to use for querying the database")
                .long_help("The identity to use for querying the database. If no identity is provided, the default one will be used."),
        )
        .arg(
            Arg::new("anon_identity")
                .long("anon-identity")
                .short('a')
                .conflicts_with("identity")
                .action(ArgAction::SetTrue)
                .help("If this flag is present, no identity will be provided when querying the database")
        )
        .arg(common_args::server()
                .help("The nickname, host name or URL of the server hosting the database"),
        )
        .arg(
            Arg::new("out_dir")
                .value_parser(clap::value_parser!(PathBuf))
                .required(true)
                .long("out-dir")
                .short('o')
                .help("The system path (absolute or relative) to the generate output directory"),
        )
        .arg(
            Arg::new("lang")
                .required(true)
                .long("lang")
                .short('l')
                .value_parser(clap::value_parser!(Language))
                .help("The language to generate"),
        )
        .after_help("Run `spacetime help publish` for more detailed information.")
}

pub async fn exec(config: Config, args: &clap::ArgMatches) -> anyhow::Result<()> {
    let out_dir = PathBuf::from(r"C:\Users/MERLI\VSCODE\bitcraft-crafting-wiki\Temp");
    let lang = Language::TypeScript;
    let namespace = "SpacetimeDB.Types";
    println!("Before Parse.");
    let conn = parse_req(config, args).await?;
    println!("parse connection.");
    let api = ClientApi::new(conn);
    println!("client api");
    let module = api.module_def().await?;
    println!("module loaded");
    fs::create_dir_all(&out_dir)?;
    let wasm_file = PathBuf::from(r"C:\Users\MERLI\VSCODE\bitcraft-crafting-wiki\Temp");
    let mut paths = vec![];
    for (fname, code) in generate(&wasm_file, lang, namespace, module)? {
        let fname = Path::new(&fname);
        // If a generator asks for a file in a subdirectory, create the subdirectory first.
        if let Some(parent) = fname.parent().filter(|p| !p.as_os_str().is_empty()) {
            fs::create_dir_all(out_dir.join(parent))?;
        }
        let path = out_dir.join(fname);
        paths.push(path.clone());
        fs::write(path, code)?;
    }

    format_files(paths.clone(), lang)?;


    println!("Generate finished successfully.");
    Ok(())
}

#[derive(Clone, Copy, PartialEq)]
pub enum Language {
    Csharp,
    TypeScript,
    Python,
    Rust,
}

impl clap::ValueEnum for Language {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Csharp, Self::TypeScript, Self::Python, Self::Rust]
    }
    fn to_possible_value(&self) -> Option<clap::builder::PossibleValue> {
        match self {
            Self::Csharp => Some(clap::builder::PossibleValue::new("csharp").aliases(["c#", "cs"])),
            Self::TypeScript => Some(clap::builder::PossibleValue::new("typescript").aliases(["ts", "TS"])),
            Self::Python => Some(clap::builder::PossibleValue::new("python").aliases(["py", "PY"])),
            Self::Rust => Some(clap::builder::PossibleValue::new("rust").aliases(["rs", "RS"])),
        }
    }
}

pub struct GenCtx {
    typespace: Typespace,
    names: Vec<Option<String>>,
}


pub fn generate<'a>(wasm_file: &'a Path, lang: Language, namespace: &'a str, module: ModuleDef) -> anyhow::Result<Vec<(String, String)>> {
    let (ctx, items) = extract_from_moduledef(module);
    let items: Vec<GenItem> = items.collect();
    let mut files: Vec<(String, String)> = items
        .iter()
        .filter_map(|item| item.generate(&ctx, lang, namespace))
        .collect();
    files.extend(generate_globals(&ctx, lang, namespace, &items));

    Ok(files)
}

fn generate_globals(ctx: &GenCtx, lang: Language, namespace: &str, items: &[GenItem]) -> Vec<(String, String)> {
    match lang {
        Language::Csharp => csharp::autogen_csharp_globals(items, namespace),
        Language::TypeScript => typescript::autogen_typescript_globals(ctx, items),
        Language::Python => python::autogen_python_globals(ctx, items),
        Language::Rust => rust::autogen_rust_globals(ctx, items),
    }
}

pub fn extract_from_moduledef(module: ModuleDef) -> (GenCtx, impl Iterator<Item = GenItem>) {
    let ModuleDef {
        typespace,
        tables,
        reducers,
        misc_exports,
    } = module;
    // HACK: Patch the fields to have the types that point to `AlgebraicTypeRef` because all generators depend on that
    // `register_table` in rt.rs resolve the types early, but the generators do it late. This impact enums where
    // the enum name is not preserved in the `AlgebraicType`.
    let tables: Vec<_> = tables
        .into_iter()
        .map(|mut x| {
            x.schema.columns = typespace[x.data].as_product().unwrap().clone().into();
            x
        })
        .collect();

    let mut names = vec![None; typespace.types.len()];
    let name_info = itertools::chain!(
        tables.iter().map(|t| (t.data, &*t.schema.table_name)),
        misc_exports
            .iter()
            .map(|MiscModuleExport::TypeAlias(a)| (a.ty, &*a.name)),
    );
    for (typeref, name) in name_info {
        names[typeref.idx()] = Some(name.into())
    }
    let ctx = GenCtx { typespace, names };
    let iter = itertools::chain!(
        misc_exports.into_iter().map(GenItem::from_misc_export),
        tables.into_iter().map(GenItem::Table),
        reducers
            .into_iter()
            .filter(|r| !(r.name.starts_with("__") && r.name.ends_with("__")))
            .map(GenItem::Reducer),
    );
    (ctx, iter)
}

pub enum GenItem {
    Table(TableDesc),
    TypeAlias(TypeAlias),
    Reducer(ReducerDef),
}

impl GenItem {
    fn from_misc_export(exp: MiscModuleExport) -> Self {
        match exp {
            MiscModuleExport::TypeAlias(a) => Self::TypeAlias(a),
        }
    }

    fn generate(&self, ctx: &GenCtx, lang: Language, namespace: &str) -> Option<(String, String)> {
        match lang {
            Language::Csharp => self.generate_csharp(ctx, namespace),
            Language::TypeScript => self.generate_typescript(ctx),
            Language::Python => self.generate_python(ctx),
            Language::Rust => self.generate_rust(ctx),
        }
    }

    fn generate_rust(&self, ctx: &GenCtx) -> Option<(String, String)> {
        match self {
            GenItem::Table(table) => {
                let code = rust::autogen_rust_table(ctx, table);
                Some((rust::rust_type_file_name(&table.schema.table_name), code))
            }
            GenItem::TypeAlias(TypeAlias { name, ty }) => {
                let code = match &ctx.typespace[*ty] {
                    AlgebraicType::Sum(sum) => rust::autogen_rust_sum(ctx, name, sum),
                    AlgebraicType::Product(prod) => rust::autogen_rust_tuple(ctx, name, prod),
                    _ => todo!(),
                };
                Some((rust::rust_type_file_name(name), code))
            }
            GenItem::Reducer(reducer) => {
                let code = rust::autogen_rust_reducer(ctx, reducer);
                Some((rust::rust_reducer_file_name(&reducer.name), code))
            }
        }
    }

    fn generate_python(&self, ctx: &GenCtx) -> Option<(String, String)> {
        match self {
            GenItem::Table(table) => {
                let code = python::autogen_python_table(ctx, table);
                let name = table.schema.table_name.deref().to_case(Case::Snake);
                Some((name + ".py", code))
            }
            GenItem::TypeAlias(TypeAlias { name, ty }) => match &ctx.typespace[*ty] {
                AlgebraicType::Sum(sum) => {
                    let filename = name.replace('.', "").to_case(Case::Snake);
                    let code = python::autogen_python_sum(ctx, name, sum);
                    Some((filename + ".py", code))
                }
                AlgebraicType::Product(prod) => {
                    let code = python::autogen_python_tuple(ctx, name, prod);
                    let name = name.to_case(Case::Snake);
                    Some((name + ".py", code))
                }
                AlgebraicType::Builtin(_) => todo!(),
                AlgebraicType::Ref(_) => todo!(),
            },
            GenItem::Reducer(reducer) => {
                let code = python::autogen_python_reducer(ctx, reducer);
                let name = reducer.name.deref().to_case(Case::Snake);
                Some((name + "_reducer.py", code))
            }
        }
    }

    fn generate_typescript(&self, ctx: &GenCtx) -> Option<(String, String)> {
        match self {
            GenItem::Table(table) => {
                let code = typescript::autogen_typescript_table(ctx, table);
                let name = table.schema.table_name.deref().to_case(Case::Snake);
                Some((name + ".ts", code))
            }
            GenItem::TypeAlias(TypeAlias { name, ty }) => match &ctx.typespace[*ty] {
                AlgebraicType::Sum(sum) => {
                    let filename = name.replace('.', "").to_case(Case::Snake);
                    let code = typescript::autogen_typescript_sum(ctx, name, sum);
                    Some((filename + ".ts", code))
                }
                AlgebraicType::Product(prod) => {
                    let code = typescript::autogen_typescript_tuple(ctx, name, prod);
                    let name = name.to_case(Case::Snake);
                    Some((name + ".ts", code))
                }
                AlgebraicType::Builtin(_) => todo!(),
                AlgebraicType::Ref(_) => todo!(),
            },
            GenItem::Reducer(reducer) => {
                let code = typescript::autogen_typescript_reducer(ctx, reducer);
                let name = reducer.name.deref().to_case(Case::Snake);
                Some((name + "_reducer.ts", code))
            }
        }
    }

    fn generate_csharp(&self, ctx: &GenCtx, namespace: &str) -> Option<(String, String)> {
        match self {
            GenItem::Table(table) => {
                let code = csharp::autogen_csharp_table(ctx, table, namespace);
                Some((table.schema.table_name.to_string() + ".cs", code))
            }
            GenItem::TypeAlias(TypeAlias { name, ty }) => match &ctx.typespace[*ty] {
                AlgebraicType::Sum(sum) => {
                    let filename = name.replace('.', "");
                    let code = csharp::autogen_csharp_sum(ctx, name, sum, namespace);
                    Some((filename + ".cs", code))
                }
                AlgebraicType::Product(prod) => {
                    let code = csharp::autogen_csharp_tuple(ctx, name, prod, namespace);
                    Some((name.clone() + ".cs", code))
                }
                AlgebraicType::Builtin(_) => todo!(),
                AlgebraicType::Ref(_) => todo!(),
            },
            GenItem::Reducer(reducer) => {
                let code = csharp::autogen_csharp_reducer(ctx, reducer, namespace);
                let pascalcase = reducer.name.deref().to_case(Case::Pascal);
                Some((pascalcase + "Reducer.cs", code))
            }
        }
    }
}

fn extract_descriptions(wasm_file: &Path) -> anyhow::Result<ModuleDef> {
    let engine = wasmtime::Engine::default();
    let t = std::time::Instant::now();
    let module = wasmtime::Module::from_file(&engine, wasm_file)?;
    println!("compilation took {:?}", t.elapsed());
    let ctx = WasmCtx {
        mem: None,
        buffers: slab::Slab::new(),
    };
    let mut store = wasmtime::Store::new(&engine, ctx);
    let mut linker = wasmtime::Linker::new(&engine);
    linker.allow_shadowing(true).define_unknown_imports_as_traps(&module)?;
    let module_name = &*format!("spacetime_{MODULE_ABI_MAJOR_VERSION}.0");
    linker.func_wrap(
        module_name,
        "_console_log",
        |caller: Caller<'_, WasmCtx>,
         _level: u32,
         _target: u32,
         _target_len: u32,
         _filename: u32,
         _filename_len: u32,
         _line_number: u32,
         message: u32,
         message_len: u32| {
            let mem = caller.data().mem.unwrap();
            let slice = mem.deref_slice(&caller, message, message_len);
            if let Some(slice) = slice {
                println!("from wasm: {}", String::from_utf8_lossy(slice));
            } else {
                println!("tried to print from wasm but out of bounds")
            }
        },
    )?;
    linker.func_wrap(module_name, "_buffer_alloc", WasmCtx::buffer_alloc)?;
    let instance = linker.instantiate(&mut store, &module)?;
    let memory = Memory {
        mem: instance.get_memory(&mut store, "memory").unwrap(),
    };
    store.data_mut().mem = Some(memory);

    let mut preinits = instance
        .exports(&mut store)
        .filter_map(|exp| Some((exp.name().strip_prefix("__preinit__")?.to_owned(), exp.into_func()?)))
        .collect::<Vec<_>>();
    preinits.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (_, func) in preinits {
        func.typed(&store)?.call(&mut store, ())?
    }
    let module = match instance.get_func(&mut store, "__describe_module__") {
        Some(f) => {
            let buf: u32 = f.typed(&store)?.call(&mut store, ()).unwrap();
            let slice = store.data_mut().buffers.remove(buf as usize);
            bsatn::from_slice(&slice)?
        }
        None => ModuleDef::default(),
    };
    Ok(module)
}

struct WasmCtx {
    mem: Option<Memory>,
    buffers: slab::Slab<Vec<u8>>,
}

impl WasmCtx {
    fn mem(&self) -> Memory {
        self.mem.unwrap()
    }
    fn buffer_alloc(mut caller: Caller<'_, Self>, data: u32, data_len: u32) -> u32 {
        let buf = caller
            .data()
            .mem()
            .deref_slice(&caller, data, data_len)
            .unwrap()
            .to_vec();
        caller.data_mut().buffers.insert(buf) as u32
    }
}

#[derive(Copy, Clone)]
struct Memory {
    mem: wasmtime::Memory,
}

impl Memory {
    fn deref_slice<'a>(&self, store: &'a impl AsContext, offset: u32, len: u32) -> Option<&'a [u8]> {
        self.mem
            .data(store.as_context())
            .get(offset as usize..)?
            .get(..len as usize)
    }
}

fn format_files(generated_files: Vec<PathBuf>, lang: Language) -> anyhow::Result<()> {
    match lang {
        Language::Rust => {
            cmd!("rustup", "component", "add", "rustfmt").run()?;
            for path in generated_files {
                cmd!("rustfmt", path.to_str().unwrap()).run()?;
            }
        }
        Language::Csharp => {}
        Language::TypeScript => {}
        Language::Python => {}
    }

    Ok(())
}
