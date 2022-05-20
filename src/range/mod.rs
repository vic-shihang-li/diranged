mod payload_range;
mod simple_range;

pub use payload_range::PayloadRange;
pub use simple_range::SimpleRange;

/// An enumeration of possible range comparison outputs.
///
/// This is used in conjunction with [`Range::compare()`].
///
/// Depending on their [`RangeMode`], two range's comparison results could
/// differ, even though the ranges have the same min and max values.
///
/// ```rust
/// use drng::{SimpleRange, RangeMode, range_compare, RangeCompareResult::*};
///
/// let r1 = SimpleRange::new(100, 200, RangeMode::Inclusive).unwrap();
/// let r2 = SimpleRange::new(200, 300, RangeMode::Inclusive).unwrap();
/// let r2_start_excl = SimpleRange::new(200, 300, RangeMode::StartExclusive).unwrap();
///
/// // r1 overlaps with the lower part of r2
/// assert_eq!(range_compare(&r1, &r2), OverlapLower);
///
/// // r1 is strictly lower than r2_start_excl
/// assert_eq!(range_compare(&r1, &r2_start_excl), LessThanNoOverlap);
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
    /// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult::*};
    ///
    /// let first  = SimpleRange::new(10, 20, RangeMode::Inclusive).unwrap();
    /// let second = SimpleRange::new(200, 300, RangeMode::Inclusive).unwrap();
    ///
    /// assert_eq!(range_compare(&first, &second), LessThanNoOverlap);
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
    /// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult::*};
    ///
    /// let second = SimpleRange::new(200, 300, RangeMode::Inclusive).unwrap();
    ///
    /// let first  = SimpleRange::new(100, 299, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), OverlapLower);
    ///
    /// let first  = SimpleRange::new(100, 300, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), Contains);
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
    /// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult::*};
    ///
    /// let first = SimpleRange::new(33, 35, RangeMode::Inclusive).unwrap();
    /// let second = SimpleRange::new(10, 990, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), Contained);
    /// assert_eq!(range_compare(&second, &first), Contains);
    ///
    /// // the first and second range share the same starting point
    /// let first = SimpleRange::new(10, 35, RangeMode::Inclusive).unwrap();
    /// let second = SimpleRange::new(10, 990, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), Contained);
    /// assert_eq!(range_compare(&second, &first), Contains);
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
    /// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult::*};
    ///
    /// let first = SimpleRange::new(10, 990, RangeMode::Inclusive).unwrap();
    /// let second = SimpleRange::new(33, 35, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), Contains);
    /// assert_eq!(range_compare(&second, &first), Contained);
    ///
    /// // the first and second range share the same starting point
    /// let first = SimpleRange::new(10, 990, RangeMode::Inclusive).unwrap();
    /// let second = SimpleRange::new(10, 35, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), Contains);
    /// assert_eq!(range_compare(&second, &first), Contained);
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
    /// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult::*};
    ///
    /// let first = SimpleRange::new(10, 15, RangeMode::Inclusive).unwrap();
    /// let first_end_excl = SimpleRange::new(10, 16, RangeMode::EndExclusive).unwrap();
    /// let first_start_excl = SimpleRange::new(9, 15, RangeMode::StartExclusive).unwrap();
    /// let first_excl = SimpleRange::new(9, 16, RangeMode::Exclusive).unwrap();
    /// let second = SimpleRange::new(10, 15, RangeMode::Inclusive).unwrap();
    ///
    /// assert_eq!(range_compare(&first, &second), Equal);
    /// assert_eq!(range_compare(&first_end_excl, &second), Equal);
    /// assert_eq!(range_compare(&first_start_excl, &second), Equal);
    /// assert_eq!(range_compare(&first_excl, &second), Equal);
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
    /// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult};
    ///
    /// let first = SimpleRange::new(13, 22, RangeMode::Inclusive).unwrap();
    /// let second = SimpleRange::new(10, 15, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), RangeCompareResult::OverlapUpper);
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
    /// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult::*};
    ///
    /// let first = SimpleRange::new(20, 25, RangeMode::Inclusive).unwrap();
    /// let second = SimpleRange::new(10, 15, RangeMode::Inclusive).unwrap();
    /// assert_eq!(range_compare(&first, &second), GreaterNoOverlap);
    /// ```
    GreaterNoOverlap,
}

/// Compares two ranges.
///
/// ```
/// use drng::{SimpleRange, range_compare, RangeMode, RangeCompareResult::*};
///
/// let first  = SimpleRange::new(10, 20, RangeMode::Inclusive).unwrap();
/// let second = SimpleRange::new(15, 33, RangeMode::Inclusive).unwrap();
///
/// assert_eq!(range_compare(&first, &second), OverlapLower);
/// ```
///
/// For more documentation, see [`RangeCompareResult`].
pub fn range_compare<R1: Range, R2: Range>(r1: &R1, r2: &R2) -> RangeCompareResult {
    let self_min_incl = r1.min_incl();
    let self_max_incl = r1.max_incl();
    let other_min_incl = r2.min_incl();
    let other_max_incl = r2.max_incl();

    if self_min_incl == other_min_incl && self_max_incl == other_max_incl {
        return RangeCompareResult::Equal;
    }

    if self_min_incl < other_min_incl {
        // self:  [....]
        // other:        [......]
        if self_max_incl < other_min_incl {
            return RangeCompareResult::LessThanNoOverlap;
        }
        // self:  [....]
        // other:    [.......]
        if other_min_incl <= self_max_incl && self_max_incl < other_max_incl {
            return RangeCompareResult::OverlapLower;
        }
        // self:  [...........]
        // other:    [......]
        return RangeCompareResult::Contains;
    }

    if self_min_incl == other_min_incl {
        // self:  [.....]
        // other: [..........]
        if self_max_incl < other_max_incl {
            return RangeCompareResult::Contained;
        }
        // self:  [..........]
        // other: [..........]
        if self_max_incl == other_max_incl {
            return RangeCompareResult::Equal;
        }
        // self:  [...............]
        // other: [..........]
        return RangeCompareResult::Contains;
    }

    if self_min_incl > other_min_incl {
        // self:        [.....]
        // other: [...]
        if other_max_incl < self_min_incl {
            return RangeCompareResult::GreaterNoOverlap;
        }
        // self:        [.....]
        // other: [.......]
        if other_max_incl >= self_min_incl && other_max_incl < self_max_incl {
            return RangeCompareResult::OverlapUpper;
        }
        // self:        [.....]
        // other: [............]
        return RangeCompareResult::Contained;
    }

    unreachable!("Non-exhaustive comparison!")
}

pub trait Range {
    /// Retrieves the min value of this range.
    fn min(&self) -> usize;

    /// Retrieves the max value of this range.
    fn max(&self) -> usize;

    fn min_incl(&self) -> usize;

    fn max_incl(&self) -> usize;

    /// Checks whether a value is part of this range.
    fn includes(&self, value: usize) -> bool;
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

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{quickcheck, TestResult};

    #[test]
    fn test_range_compare_eq() {
        fn prop_comp_eq(r1: SimpleRange, r2: SimpleRange) -> TestResult {
            match range_compare(&r1, &r2) {
                RangeCompareResult::Equal => {
                    let valid = r1.min_incl() == r2.min_incl() && r1.max_incl() == r2.max_incl();
                    TestResult::from_bool(valid)
                }
                _ => TestResult::discard(),
            }
        }

        fn prop_range_eq_self(r: SimpleRange) -> bool {
            range_compare(&r, &r) == RangeCompareResult::Equal
        }

        quickcheck(prop_range_eq_self as fn(SimpleRange) -> bool);
        quickcheck(prop_comp_eq as fn(SimpleRange, SimpleRange) -> TestResult);
    }

    #[quickcheck]
    fn test_range_less_than_no_overlap(r1: SimpleRange, r2: SimpleRange) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::LessThanNoOverlap => {
                TestResult::from_bool(r1.max_incl() < r2.min_incl())
            }
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn test_range_compare_overlap_lower(r1: SimpleRange, r2: SimpleRange) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::OverlapLower => TestResult::from_bool(
                r1.min_incl() < r2.min_incl()
                    && r1.max_incl() >= r2.min_incl()
                    && r1.min_incl() <= r2.max_incl(),
            ),
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn test_range_compare_contained(r1: SimpleRange, r2: SimpleRange) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::Contained => TestResult::from_bool(
                !(r1.min_incl() == r2.min_incl() && r1.max_incl() == r2.max_incl())
                    && r1.min_incl() >= r2.min_incl()
                    && r1.max_incl() <= r2.max_incl(),
            ),
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn test_range_compare_contains(r1: SimpleRange, r2: SimpleRange) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::Contains => TestResult::from_bool(
                !(r1.min_incl() == r2.min_incl() && r1.max_incl() == r2.max_incl())
                    && r1.min_incl() <= r2.min_incl()
                    && r1.max_incl() >= r2.max_incl(),
            ),
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn test_range_compare_contains_inverse_is_contained(
        r1: SimpleRange,
        r2: SimpleRange,
    ) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::Contains => {
                TestResult::from_bool(range_compare(&r2, &r1) == RangeCompareResult::Contained)
            }
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn test_range_compare_contained_inverse_is_contains(
        r1: SimpleRange,
        r2: SimpleRange,
    ) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::Contained => {
                TestResult::from_bool(range_compare(&r2, &r1) == RangeCompareResult::Contains)
            }
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn test_range_compare_overlap_upper(r1: SimpleRange, r2: SimpleRange) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::OverlapUpper => TestResult::from_bool(
                (r1.min_incl() >= r2.min_incl() && r1.min_incl() <= r2.max_incl())
                    && r1.max_incl() > r2.max_incl(),
            ),
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn test_range_compare_greater_no_overlap(r1: SimpleRange, r2: SimpleRange) -> TestResult {
        match range_compare(&r1, &r2) {
            RangeCompareResult::GreaterNoOverlap => {
                TestResult::from_bool(r1.min_incl() > r2.max_incl())
            }
            _ => TestResult::discard(),
        }
    }
}
