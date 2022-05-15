//! A disjoint range implementation.

#![warn(missing_docs)]

/// An explanation of why an overlap error occurred while inserting to a
/// [`DisjointRange`].
#[derive(Debug)]
pub struct OverlapError {
    kind: RangeCompareResult,
    other: Range,
}

/// Possible errors when inserting a range to a [`DisjointRange`].
#[derive(Debug)]
pub enum AddError {
    /// Insertion erred because the range to insert overlaps with an existing
    /// range in [`DisjointRange`].
    OverlapRange(OverlapError),
    /// Insertion failed because the provided parameters does not form a vaild
    /// range (e.g., when the start value is greater than the end value).
    BadRange,
}

/// An enumeration of inclusive / exclusiveness on both ends of a range.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum RangeMode {
    /// Range where the start and end are inclusive (i.e., [start..end]).
    Inclusive,
    /// Range where the start and end are exclusive (i.e., (start..end)).
    Exclusive,
    /// Range where the start is exclusive and the end is inclusive
    /// (i.e., (start..end]).
    StartExclusive,
    /// Range where the start is inclusive and the end is exclusive
    /// (i.e., [start..end)).
    EndExclusive,
}

/// A data structure holding a disjoint set of ranges.
///
/// The following code snippet represents a set of ranges:
///
/// ```rust
/// use drng::{DisjointRange, RangeMode};
/// let mut dr = DisjointRange::new(RangeMode::Inclusive);
///
/// // not drawn to scale
/// // 0.......[35..90][91..110]..[115, 120]
///
/// dr.add(35, 90).unwrap();
/// dr.add(91, 110).unwrap();
/// dr.add(115, 120).unwrap();
///
/// assert!(dr.includes(35));
/// assert!(!dr.includes(113));
/// ```
pub struct DisjointRange {
    ranges: Vec<Range>,
    mode: RangeMode,
}

impl DisjointRange {
    /// Creates a new [`DisjointRange`].
    pub fn new(mode: RangeMode) -> Self {
        Self {
            ranges: Vec::new(),
            mode,
        }
    }

    /// Adds a range to this [`DisjointRange`].
    pub fn add(self: &mut Self, min: usize, max: usize) -> Result<(), AddError> {
        match Range::new(min, max, self.mode) {
            Err(_) => Err(AddError::BadRange),
            Ok(range_to_insert) => {
                for (i, range) in self.ranges.iter().enumerate() {
                    match range_to_insert.compare_with(&range) {
                        RangeCompareResult::GreaterNoOverlap => continue,
                        RangeCompareResult::LessThanNoOverlap => {
                            self.ranges.insert(i, range_to_insert);
                            return Ok(());
                        }
                        r => {
                            return Err(AddError::OverlapRange(OverlapError {
                                kind: r,
                                other: *range,
                            }))
                        }
                    }
                }

                self.ranges.push(range_to_insert);

                Ok(())
            }
        }
    }

    /// Checks whether the given value falls into one of the ranges.
    pub fn includes(&self, value: usize) -> bool {
        self.lookup(value).is_some()
    }

    /// Checks if the data structure contains the provided value.
    ///
    /// If yes, return the range that contains this value.
    pub fn lookup(&self, value: usize) -> Option<&Range> {
        self.ranges.iter().find(|r| r.includes(value))
    }

    /// Iterates this [`DisjointRange`] in range-ascending order.
    pub fn iter(self: &Self) -> DisjointRangeIter {
        DisjointRangeIter::new(self)
    }
}

/// Iterates a [`DisjointRange`].
pub struct DisjointRangeIter<'a> {
    dr: &'a DisjointRange,
    curr: usize,
}

impl<'a> DisjointRangeIter<'a> {
    fn new(dr: &'a DisjointRange) -> DisjointRangeIter<'a> {
        Self { dr, curr: 0 }
    }
}

impl<'a> Iterator for DisjointRangeIter<'a> {
    type Item = Range;

    fn next(&mut self) -> Option<Self::Item> {
        match self.dr.ranges.get(self.curr) {
            Some(range) => {
                self.curr += 1;
                Some(*range)
            }
            None => None,
        }
    }
}

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
#[derive(Debug)]
pub enum BadRange {
    /// Errs when the provided min value is greater than the max value.
    MinGreaterThanMax,
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
            RangeMode::StartExclusive => new_inclusive(min + 1, max),
            RangeMode::EndExclusive => new_inclusive(min, max - 1),
            RangeMode::Exclusive => new_inclusive(min + 1, max - 1),
        }
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

    fn includes(&self, value: usize) -> bool {
        value >= self.min_incl && value <= self.max_incl
    }

    fn compare_with(&self, other: &Range) -> RangeCompareResult {
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

    #[test]
    fn create_basic_dr() {
        let sorted_sequence = [
            [100, 200],
            [222, 235],
            [20000, 22322],
            [34330, 50000],
            [60000, 700000],
        ];
        let mut dr = DisjointRange::new(RangeMode::Inclusive);
        insert_ranges(&mut dr, &sorted_sequence);
        assert_range_sequence(&dr, &sorted_sequence);
    }

    #[test]
    fn add_overlapping_range_errs() {
        let mut dr = DisjointRange::new(RangeMode::Inclusive);
        dr.add(100, 200).unwrap();
        assert_insert_overlaps(dr.add(90, 111), RangeCompareResult::OverlapLower);
        assert_insert_overlaps(dr.add(100, 123), RangeCompareResult::Contained);
        assert_insert_overlaps(dr.add(140, 160), RangeCompareResult::Contained);
        assert_insert_overlaps(dr.add(188, 200), RangeCompareResult::Contained);
        assert_insert_overlaps(dr.add(100, 200), RangeCompareResult::Equal);
        assert_insert_overlaps(dr.add(100, 300), RangeCompareResult::Contains);
        assert_insert_overlaps(dr.add(73, 2000), RangeCompareResult::Contains);
        assert_insert_overlaps(dr.add(180, 222), RangeCompareResult::OverlapUpper);
        assert_insert_overlaps(dr.add(200, 222), RangeCompareResult::OverlapUpper);
    }

    #[test]
    fn add_invalid_inclusive_range() {
        let mut dr = DisjointRange::new(RangeMode::Inclusive);
        assert_add_bad_range_errs(dr.add(100, 80));
        assert!(dr.add(50, 50).is_ok());
    }

    #[test]
    fn add_invalid_end_exclusive_range() {
        let mut dr = DisjointRange::new(RangeMode::EndExclusive);
        assert!(dr.add(9, 10).is_ok());
        assert_add_bad_range_errs(dr.add(100, 80));
        assert_add_bad_range_errs(dr.add(50, 50));
    }

    #[test]
    fn add_invalid_start_exclusive_range() {
        let mut dr = DisjointRange::new(RangeMode::StartExclusive);
        assert!(dr.add(9, 10).is_ok());
        assert_add_bad_range_errs(dr.add(100, 80));
        assert_add_bad_range_errs(dr.add(50, 50));
    }

    #[test]
    fn add_invalid_exclusive_range() {
        let mut dr = DisjointRange::new(RangeMode::Exclusive);
        assert_add_bad_range_errs(dr.add(100, 80));
        assert_add_bad_range_errs(dr.add(50, 50));
        assert_add_bad_range_errs(dr.add(49, 50));
        assert!(dr.add(48, 50).is_ok());
    }

    #[test]
    fn add_unordered_ranges() {
        let mut dr = DisjointRange::new(RangeMode::Inclusive);
        insert_ranges(
            &mut dr,
            &[
                [100, 200],
                [30, 50],
                [1, 2],
                [60, 66],
                [500, 555],
                [343, 444],
            ],
        );
        assert_range_sequence(
            &dr,
            &[
                [1, 2],
                [30, 50],
                [60, 66],
                [100, 200],
                [343, 444],
                [500, 555],
            ],
        );
    }

    #[test]
    fn end_exclusive_dr() {
        let mut dr = DisjointRange::new(RangeMode::EndExclusive);
        insert_ranges(
            &mut dr,
            &[
                [100, 200],
                [99, 100],
                [98, 99],
                [30, 50],
                [50, 70],
                [70, 90],
                [211, 212],
                [209, 211],
            ],
        );
        assert_range_sequence(
            &dr,
            &[
                [30, 50],
                [50, 70],
                [70, 90],
                [98, 99],
                [99, 100],
                [100, 200],
                [209, 211],
                [211, 212],
            ],
        );
    }

    #[test]
    fn find_value_in_range() {
        let mut dr = DisjointRange::new(RangeMode::EndExclusive);

        dr.add(100, 200).unwrap();
        assert!(dr.includes(100));
        assert!(dr.includes(105));
        assert!(dr.includes(199));
        assert!(!dr.includes(200));
        assert!(!dr.includes(201));
        assert!(!dr.includes(3));
        assert!(!dr.includes(30000));
    }

    #[test]
    fn lookup_range() {
        let mut dr = DisjointRange::new(RangeMode::EndExclusive);

        insert_ranges(&mut dr, &[[100, 200], [300, 4500]]);

        let found_fst = dr.lookup(199).unwrap();
        assert_range_min_max(found_fst, 100, 200);

        assert!(dr.lookup(200).is_none());
        assert!(dr.lookup(248).is_none());

        let found_snd = dr.lookup(344).unwrap();
        assert_range_min_max(found_snd, 300, 4500);
    }

    fn insert_ranges(dr: &mut DisjointRange, seq: &[[usize; 2]]) {
        seq.iter().for_each(|[min, max]| {
            dr.add(*min, *max)
                .expect(format!("failed to insert min: {}, max: {}", min, max).as_str());
        })
    }

    fn assert_range_sequence(dr: &DisjointRange, seq: &[[usize; 2]]) {
        let mut dr_iter = dr.iter();
        let mut deq_iter = seq.iter();

        loop {
            match dr_iter.next() {
                None => match deq_iter.next() {
                    None => break,
                    Some(r) => panic!(
                        "Reached disjoint range end while the expected \
                               next range is {:?}",
                        r
                    ),
                },
                Some(got) => match deq_iter.next() {
                    None => panic!(
                        "Disjoint range longer than expected; \
                                   got {:?} while expected sequence ended",
                        got
                    ),
                    Some([expected_min, expected_max]) => {
                        assert_range_min_max(&got, *expected_min, *expected_max)
                    }
                },
            }
        }
    }

    fn assert_range_min_max(range: &Range, min: usize, max: usize) {
        assert_eq!(range.min(), min);
        assert_eq!(range.max(), max);
    }

    fn assert_add_bad_range_errs(add_result: Result<(), AddError>) {
        match add_result {
            Ok(_) => panic!("add bad range should fail"),
            Err(e) => match e {
                AddError::BadRange => (),
                _ => panic!("expected bad range, got {:?}", e),
            },
        }
    }

    fn assert_insert_overlaps(add_result: Result<(), AddError>, kind: RangeCompareResult) {
        match add_result {
            Ok(_) => panic!("expected add to fail"),
            Err(e) => match e {
                AddError::OverlapRange(x) => assert_eq!(x.kind, kind),
                _ => panic!("expected overlap range error, got {:?}", e),
            },
        }
    }
}
