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
