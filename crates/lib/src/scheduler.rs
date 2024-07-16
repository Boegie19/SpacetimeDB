use std::{fmt::Debug, time::Duration};

use spacetimedb_sats::{
    algebraic_value::de::{ValueDeserializeError, ValueDeserializer},
    de::Deserialize as _,
    AlgebraicValue, SpacetimeType,
};

/// When a scheduled reducer should execute,
/// either at a specific point in time,
/// or at regular intervals for repeating schedules.
///
/// Stored in reducer-scheduling tables as a column.
#[derive(SpacetimeType, Copy, Clone, PartialEq, Eq, Debug)]
#[sats(crate = spacetimedb_sats)]
pub enum ScheduleAt {
    /// A specific time to which the reducer is scheduled.
    /// Value is a UNIX timestamp in microseconds.
    Time(u64),
    /// A regular interval at which the repeated reducer is scheduled.
    /// Value is a duration in microseconds.
    Interval(u64),
}

impl ScheduleAt {
    /// Converts the `ScheduleAt` to a `std::time::Duration` from now.
    pub fn to_duration_from_now(&self) -> std::time::Duration {
        match self {
            ScheduleAt::Time(time) => {
                let now = std::time::SystemTime::now();
                // Safety: Now is always after UNIX_EPOCH.
                let now = now.duration_since(std::time::UNIX_EPOCH).unwrap();
                let time = std::time::Duration::from_micros(*time);
                time.checked_sub(now).unwrap_or(Duration::from_micros(0))
            }
            ScheduleAt::Interval(dur) => Duration::from_micros(*dur),
        }
    }
}

impl From<std::time::Duration> for ScheduleAt {
    fn from(value: std::time::Duration) -> Self {
        ScheduleAt::Interval(value.as_micros() as u64)
    }
}

impl TryFrom<AlgebraicValue> for ScheduleAt {
    type Error = ValueDeserializeError;
    fn try_from(value: AlgebraicValue) -> Result<Self, Self::Error> {
        ScheduleAt::deserialize(ValueDeserializer::new(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use spacetimedb_sats::bsatn;

    #[test]
    fn test_bsatn_roundtrip() {
        let schedule_at = ScheduleAt::Interval(10000);
        let ser = bsatn::to_vec(&schedule_at).unwrap();
        let de = bsatn::from_slice(&ser).unwrap();
        assert_eq!(schedule_at, de);
    }
}
