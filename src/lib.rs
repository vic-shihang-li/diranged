#[derive(Debug)]
pub struct OverlapContext {
    kind: RangeCompareResult,
    other: Range,
}

#[derive(Debug)]
pub enum AddError {
    OverlapRange(OverlapContext),
    BadRange(BadRange),
}

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

pub struct DisjointRange {
    ranges: Vec<Range>,
    mode: RangeMode,
}

impl DisjointRange {
    pub fn new(mode: RangeMode) -> Self {
        Self {
            ranges: Vec::new(),
            mode,
        }
    }

    pub fn add(self: &mut Self, min: usize, max: usize) -> Result<(), AddError> {
        match Range::new(min, max, self.mode) {
            Err(e) => Err(AddError::BadRange(e)),
            Ok(range_to_insert) => {
                for (i, range) in self.ranges.iter().enumerate() {
                    match range.compare_with(&range_to_insert) {
                        RangeCompareResult::LessThanNoOverlap => continue,
                        RangeCompareResult::GreaterNoOverlap => {
                            self.ranges.insert(i, range_to_insert);
                            return Ok(());
                        }
                        r => {
                            return Err(AddError::OverlapRange(OverlapContext {
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

    pub fn iter(self: &Self) -> DisjointRangeIter {
        DisjointRangeIter::new(self)
    }
}

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

#[derive(Debug)]
enum RangeCompareResult {
    LessThanNoOverlap,
    OverlapUpper,
    Contained,
    Contains,
    Equal,
    OverlapLower,
    GreaterNoOverlap,
}

#[derive(Debug)]
pub enum BadRange {
    MinGreaterThanMax,
}

#[derive(Copy, Clone, Debug)]
pub struct Range {
    min: usize,
    max: usize,
    min_incl: usize,
    max_incl: usize,
}

impl Range {
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

    pub fn min(&self) -> usize {
        self.min
    }

    pub fn max(&self) -> usize {
        self.max
    }

    fn min_incl(&self) -> usize {
        self.min_incl
    }

    fn max_incl(&self) -> usize {
        self.max_incl
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
                return RangeCompareResult::OverlapUpper;
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
                return RangeCompareResult::OverlapLower;
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
        let mut dr = DisjointRange::new(RangeMode::Inclusive);
        dr.add(100, 200).unwrap();
        dr.add(222, 235).unwrap();
        dr.add(4000, 5000).unwrap();

        let mut iter = dr.iter();
        let r1 = iter.next().unwrap();
        assert_range_min_max(&r1, 100, 200);
        let r2 = iter.next().unwrap();
        assert_range_min_max(&r2, 222, 235);
        let r3 = iter.next().unwrap();
        assert_range_min_max(&r3, 4000, 5000);
    }

    fn assert_range_min_max(range: &Range, min: usize, max: usize) {
        assert_eq!(range.min(), min);
        assert_eq!(range.max(), max);
    }
}
