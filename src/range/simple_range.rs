use crate::range::{BadRange, Range};
use crate::RangeMode;

/// A range is a pair of min and max values.
#[derive(Copy, Clone, Debug)]
pub struct SimpleRange {
    min: usize,
    max: usize,
    min_incl: usize,
    max_incl: usize,
}

impl SimpleRange {
    /// Constructs a new [`SimpleRange`].
    pub fn new(min: usize, max: usize, mode: RangeMode) -> Result<Self, BadRange> {
        let new_inclusive = |min_incl: usize, max_incl: usize| {
            if min_incl > max_incl {
                return Err(BadRange::MinGreaterThanMax);
            }

            Ok(Self {
                min,
                max,
                min_incl,
                max_incl,
            })
        };

        match mode {
            RangeMode::Inclusive => new_inclusive(min, max),
            RangeMode::StartExclusive => match min {
                usize::MAX => Err(BadRange::InclusiveMinOverflows),
                _ => new_inclusive(min + 1, max),
            },
            RangeMode::EndExclusive => match max {
                0 => Err(BadRange::InclusiveMaxUnderflows),
                _ => new_inclusive(min, max - 1),
            },
            RangeMode::Exclusive => match min {
                usize::MAX => Err(BadRange::InclusiveMinOverflows),
                _ => match max {
                    0 => Err(BadRange::InclusiveMaxUnderflows),
                    _ => new_inclusive(min + 1, max - 1),
                },
            },
        }
    }

    /// Constructs a new [`Range`] where both `min` and `max` are part of the
    /// range.
    pub fn new_inclusive(min: usize, max: usize) -> Result<Self, BadRange> {
        SimpleRange::new(min, max, RangeMode::Inclusive)
    }

    /// Constructs a new [`Range`] where neither `min` nor `max` are part of
    /// the range.
    pub fn new_exclusive(min: usize, max: usize) -> Result<Self, BadRange> {
        SimpleRange::new(min, max, RangeMode::Exclusive)
    }

    /// Constructs a new [`Range`] where `min` is not part of the range, but
    /// `max` is.
    pub fn new_start_exclusive(min: usize, max: usize) -> Result<Self, BadRange> {
        SimpleRange::new(min, max, RangeMode::StartExclusive)
    }

    /// Constructs a new [`Range`] where `min` is part of the range, but not `max`.
    pub fn new_end_exclusive(min: usize, max: usize) -> Result<Self, BadRange> {
        SimpleRange::new(min, max, RangeMode::EndExclusive)
    }
}

impl Range for SimpleRange {
    fn min(&self) -> usize {
        self.min
    }

    fn max(&self) -> usize {
        self.max
    }

    fn min_incl(&self) -> usize {
        self.min_incl
    }

    fn max_incl(&self) -> usize {
        self.max_incl
    }

    fn includes(&self, value: usize) -> bool {
        value >= self.min_incl && value <= self.max_incl
    }
}

#[cfg(test)]
use quickcheck::{Arbitrary, Gen};

#[cfg(test)]
impl Arbitrary for SimpleRange {
    fn arbitrary(g: &mut Gen) -> SimpleRange {
        loop {
            match SimpleRange::new(
                usize::arbitrary(g),
                usize::arbitrary(g),
                RangeMode::arbitrary(g),
            ) {
                Err(_) => continue,
                Ok(r) => return r,
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::quickcheck;
    use quickcheck::TestResult;

    #[test]
    fn create_inclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match SimpleRange::new_inclusive(min, max) {
                Ok(_) => min <= max,
                Err(_) => min > max,
            }
        }

        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn create_exclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match SimpleRange::new_exclusive(min, max) {
                Ok(_) => min + 1 <= max - 1,
                Err(_) => max < 2 || min > max - 2,
            }
        }

        assert_eq!(
            SimpleRange::new_exclusive(usize::MAX, 1).unwrap_err(),
            BadRange::InclusiveMinOverflows
        );
        assert_eq!(
            SimpleRange::new_exclusive(0, 0).unwrap_err(),
            BadRange::InclusiveMaxUnderflows
        );
        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn create_start_exclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match SimpleRange::new_start_exclusive(min, max) {
                Ok(_) => min + 1 <= max,
                Err(_) => min == usize::MAX || min + 1 > max,
            }
        }

        assert_eq!(
            SimpleRange::new_start_exclusive(usize::MAX, 1).unwrap_err(),
            BadRange::InclusiveMinOverflows
        );
        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn create_end_exclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match SimpleRange::new_end_exclusive(min, max) {
                Ok(_) => min <= max - 1,
                Err(_) => max == 0 || min > max - 1,
            }
        }

        assert_eq!(
            SimpleRange::new_end_exclusive(0, 0).unwrap_err(),
            BadRange::InclusiveMaxUnderflows
        );
        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn verify_inclusive_bounds() {
        fn prop_max_incl_ge_min_incl(min: usize, max: usize, mode: RangeMode) -> TestResult {
            match SimpleRange::new(min, max, mode) {
                Ok(r) => TestResult::from_bool(r.max_incl() >= r.min_incl()),
                Err(_) => TestResult::discard(),
            }
        }

        quickcheck(prop_max_incl_ge_min_incl as fn(usize, usize, RangeMode) -> TestResult);
    }

    #[test]
    fn test_includes() {
        fn prop_included_value_within_incl_bounds(
            min: usize,
            max: usize,
            mode: RangeMode,
            value: usize,
        ) -> TestResult {
            match SimpleRange::new(min, max, mode) {
                Err(_) => TestResult::discard(),
                Ok(r) => TestResult::from_bool(
                    r.includes(value) == (value >= r.min_incl() && value <= r.max_incl()),
                ),
            }
        }

        quickcheck(
            prop_included_value_within_incl_bounds
                as fn(usize, usize, RangeMode, usize) -> TestResult,
        );
    }
}
