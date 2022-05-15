use crate::RangeMode;

/// An enumeration of possible range comparison outputs.
///
/// This is used in conjunction with [`Range::compare()`].
///
/// Depending on their [`RangeMode`], two range's comparison results could
/// differ, even though the ranges have the same min and max values.
///
/// ```rust
/// use drng::{Range, RangeMode, RangeCompareResult::*};
///
/// let r1 = Range::new(100, 200, RangeMode::Inclusive).unwrap();
/// let r2 = Range::new(200, 300, RangeMode::Inclusive).unwrap();
/// let r2_start_excl = Range::new(200, 300, RangeMode::StartExclusive).unwrap();
///
/// // r1 overlaps with the lower part of r2
/// assert_eq!(Range::compare(&r1, &r2), OverlapLower);
///
/// // r1 is strictly lower than r2_start_excl
/// assert_eq!(Range::compare(&r1, &r2_start_excl), LessThanNoOverlap);
/// ```
#[derive(Debug, PartialEq, Eq)]
pub enum RangeCompareResult {
    /// The first range is strictly lower than the second range. They do not
    /// overlap with one another.
    ///
    /// ```txt
    /// First:    xxxxxxx
    /// Second:              xxxxxx
    /// ```
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult::*};
    ///
    /// let first  = Range::new(10, 20, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(200, 300, RangeMode::Inclusive).unwrap();
    ///
    /// assert_eq!(Range::compare(&first, &second), LessThanNoOverlap);
    /// ```
    LessThanNoOverlap,
    /// The first range overlaps with the lower part of the second range.
    ///
    /// ```txt
    /// First:  xxxxxxxx
    /// Second:     xxxxxxxx
    /// ```
    ///
    /// Note that once the first range's end-exclusive value equals the second
    /// range's end-exclusive value, the first range no longer overlaps with
    /// the second. In this case, the first one "contains" the second.
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult::*};
    ///
    /// let second = Range::new(200, 300, RangeMode::Inclusive).unwrap();
    ///
    /// let first  = Range::new(100, 299, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), OverlapLower);
    ///
    /// let first  = Range::new(100, 300, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), Contains);
    /// ```
    OverlapLower,
    /// The first range is strictly smaller than the second range.
    ///
    /// ```txt
    /// First:         xxx
    /// Second:    xxxxxxxxxxxxx
    /// ```
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult::*};
    ///
    /// let first = Range::new(33, 35, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(10, 990, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), Contained);
    /// assert_eq!(Range::compare(&second, &first), Contains);
    ///
    /// // the first and second range share the same starting point
    /// let first = Range::new(10, 35, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(10, 990, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), Contained);
    /// assert_eq!(Range::compare(&second, &first), Contains);
    /// ```
    Contained,
    /// The second range is strictly larger than the first range.
    ///
    /// ```txt
    /// First:    xxxxxxxxxxxxx
    /// Second:         xxx
    /// ```
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult::*};
    ///
    /// let first = Range::new(10, 990, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(33, 35, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), Contains);
    /// assert_eq!(Range::compare(&second, &first), Contained);
    ///
    /// // the first and second range share the same starting point
    /// let first = Range::new(10, 990, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(10, 35, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), Contains);
    /// assert_eq!(Range::compare(&second, &first), Contained);
    /// ```
    Contains,
    /// The first range and the second range are range-equal.
    ///
    /// ```txt
    /// First:  xxxxxxx
    /// Second: xxxxxxx
    /// ```
    ///
    /// Depending on their [`RangeMode`], two ranges could equal one another
    /// even though their min and max value are not exactly the same.
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult::*};
    ///
    /// let first = Range::new(10, 15, RangeMode::Inclusive).unwrap();
    /// let first_end_excl = Range::new(10, 16, RangeMode::EndExclusive).unwrap();
    /// let first_start_excl = Range::new(9, 15, RangeMode::StartExclusive).unwrap();
    /// let first_excl = Range::new(9, 16, RangeMode::Exclusive).unwrap();
    /// let second = Range::new(10, 15, RangeMode::Inclusive).unwrap();
    ///
    /// assert_eq!(Range::compare(&first, &second), Equal);
    /// assert_eq!(Range::compare(&first_end_excl, &second), Equal);
    /// assert_eq!(Range::compare(&first_start_excl, &second), Equal);
    /// assert_eq!(Range::compare(&first_excl, &second), Equal);
    /// ```
    Equal,
    /// The first range overlaps with the upper part of the second range.
    ///
    /// ```txt
    /// First:     xxxxxxx
    /// Second:  xxxxx
    /// ```
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult};
    ///
    /// let first = Range::new(13, 22, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(10, 15, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), RangeCompareResult::OverlapUpper);
    /// ```
    OverlapUpper,
    /// The first range is strictly greater than the second range. They do
    /// not overlap one another.
    ///
    /// ```txt
    /// First:          xxxxxxx
    /// Second: xxxxx
    /// ```
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult::*};
    ///
    /// let first = Range::new(20, 25, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(10, 15, RangeMode::Inclusive).unwrap();
    /// assert_eq!(Range::compare(&first, &second), GreaterNoOverlap);
    /// ```
    GreaterNoOverlap,
}

/// An enumeration of possible bad [`Range`] initialization arguments.
#[derive(Debug, PartialEq, Eq)]
pub enum BadRange {
    /// Errs when the provided min value is greater than the max value.
    MinGreaterThanMax,
    /// Errs when calculating the inclusive min overflows
    InclusiveMinOverflows,
    /// Errs when calculating the inclusive max underflows
    InclusiveMaxUnderflows,
}

/// A range is a pair of min and max values.
#[derive(Copy, Clone, Debug)]
pub struct Range {
    min: usize,
    max: usize,
    min_incl: usize,
    max_incl: usize,
}

impl Range {
    /// Compares two ranges.
    ///
    /// ```
    /// use drng::{Range, RangeMode, RangeCompareResult::*};
    ///
    /// let first  = Range::new(10, 20, RangeMode::Inclusive).unwrap();
    /// let second = Range::new(15, 33, RangeMode::Inclusive).unwrap();
    ///
    /// assert_eq!(Range::compare(&first, &second), OverlapLower);
    /// ```
    ///
    /// For more documentation, see [`RangeCompareResult`].
    pub fn compare(r1: &Range, r2: &Range) -> RangeCompareResult {
        r1.compare_with(r2)
    }
}

impl Range {
    /// Constructs a new [`Range`].
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
        Range::new(min, max, RangeMode::Inclusive)
    }

    /// Constructs a new [`Range`] where neither `min` nor `max` are part of
    /// the range.
    pub fn new_exclusive(min: usize, max: usize) -> Result<Self, BadRange> {
        Range::new(min, max, RangeMode::Exclusive)
    }

    /// Constructs a new [`Range`] where `min` is not part of the range, but
    /// `max` is.
    pub fn new_start_exclusive(min: usize, max: usize) -> Result<Self, BadRange> {
        Range::new(min, max, RangeMode::StartExclusive)
    }

    /// Constructs a new [`Range`] where `min` is part of the range, but not `max`.
    pub fn new_end_exclusive(min: usize, max: usize) -> Result<Self, BadRange> {
        Range::new(min, max, RangeMode::EndExclusive)
    }

    /// Retrieves the min value of this range.
    pub fn min(&self) -> usize {
        self.min
    }

    /// Retrieves the max value of this range.
    pub fn max(&self) -> usize {
        self.max
    }

    fn min_incl(&self) -> usize {
        self.min_incl
    }

    fn max_incl(&self) -> usize {
        self.max_incl
    }

    /// Checks whether a value is part of this range.
    pub fn includes(&self, value: usize) -> bool {
        value >= self.min_incl && value <= self.max_incl
    }

    /// Compares this range with another range.
    pub fn compare_with(&self, other: &Range) -> RangeCompareResult {
        let other_min_incl = other.min_incl();
        let other_max_incl = other.max_incl();

        if self.min_incl == other_min_incl && self.max_incl == other_max_incl {
            return RangeCompareResult::Equal;
        }

        if self.min_incl < other.min_incl {
            // self:  [....]
            // other:        [......]
            if self.max_incl < other.min_incl {
                return RangeCompareResult::LessThanNoOverlap;
            }
            // self:  [....]
            // other:    [.......]
            if other.min_incl <= self.max_incl && self.max_incl < other.max_incl {
                return RangeCompareResult::OverlapLower;
            }
            // self:  [...........]
            // other:    [......]
            return RangeCompareResult::Contains;
        }

        if self.min_incl == other.min_incl {
            // self:  [.....]
            // other: [..........]
            if self.max_incl < other.max_incl {
                return RangeCompareResult::Contained;
            }
            // self:  [..........]
            // other: [..........]
            if self.max_incl == other.max_incl {
                return RangeCompareResult::Equal;
            }
            // self:  [...............]
            // other: [..........]
            return RangeCompareResult::Contains;
        }

        if self.min_incl > other.min_incl {
            // self:        [.....]
            // other: [...]
            if other.max_incl < self.min_incl {
                return RangeCompareResult::GreaterNoOverlap;
            }
            // self:        [.....]
            // other: [.......]
            if other.max_incl >= self.min_incl && other.max_incl < self.max_incl {
                return RangeCompareResult::OverlapUpper;
            }
            // self:        [.....]
            // other: [............]
            return RangeCompareResult::Contained;
        }

        unreachable!("Non-exhaustive comparison!")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{quickcheck, Arbitrary, Gen, TestResult};
    use rand::Rng;

    impl Arbitrary for RangeMode {
        fn arbitrary(_g: &mut Gen) -> RangeMode {
            let num: usize = rand::thread_rng().gen_range(0..3);
            match num {
                0 => RangeMode::Inclusive,
                1 => RangeMode::Exclusive,
                2 => RangeMode::StartExclusive,
                3 => RangeMode::EndExclusive,
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn create_inclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match Range::new_inclusive(min, max) {
                Ok(_) => min <= max,
                Err(_) => min > max,
            }
        }

        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn create_exclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match Range::new_exclusive(min, max) {
                Ok(_) => min + 1 <= max - 1,
                Err(_) => max < 2 || min > max - 2,
            }
        }

        assert_eq!(
            Range::new_exclusive(usize::MAX, 1).unwrap_err(),
            BadRange::InclusiveMinOverflows
        );
        assert_eq!(
            Range::new_exclusive(0, 0).unwrap_err(),
            BadRange::InclusiveMaxUnderflows
        );
        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn create_start_exclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match Range::new_start_exclusive(min, max) {
                Ok(_) => min + 1 <= max,
                Err(_) => min == usize::MAX || min + 1 > max,
            }
        }

        assert_eq!(
            Range::new_start_exclusive(usize::MAX, 1).unwrap_err(),
            BadRange::InclusiveMinOverflows
        );
        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn create_end_exclusive_ranges() {
        fn prop_max_greater_than_min(min: usize, max: usize) -> bool {
            match Range::new_end_exclusive(min, max) {
                Ok(_) => min <= max - 1,
                Err(_) => max == 0 || min > max - 1,
            }
        }

        assert_eq!(
            Range::new_end_exclusive(0, 0).unwrap_err(),
            BadRange::InclusiveMaxUnderflows
        );
        quickcheck(prop_max_greater_than_min as fn(usize, usize) -> bool);
    }

    #[test]
    fn verify_inclusive_bounds() {
        fn prop_max_incl_ge_min_incl(min: usize, max: usize, mode: RangeMode) -> TestResult {
            match Range::new(min, max, mode) {
                Ok(r) => TestResult::from_bool(r.max_incl >= r.min_incl),
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
            match Range::new(min, max, mode) {
                Err(_) => TestResult::discard(),
                Ok(r) => TestResult::from_bool(
                    r.includes(value) == (value >= r.min_incl && value <= r.max_incl),
                ),
            }
        }

        quickcheck(
            prop_included_value_within_incl_bounds
                as fn(usize, usize, RangeMode, usize) -> TestResult,
        );
    }
}
