use crate::range::BadRange;
use crate::range::SimpleRange;
use crate::Range;
use crate::RangeMode;

#[allow(dead_code)]
pub struct PayloadRange<'a, D> {
    range: SimpleRange,
    data: &'a D,
}

#[allow(dead_code)]
impl<'a, D> PayloadRange<'a, D> {
    /// Creates a new [`PayloadRange`].
    pub fn new(min: usize, max: usize, mode: RangeMode, data: &'a D) -> Result<Self, BadRange> {
        Ok(Self {
            range: SimpleRange::new(min, max, mode)?,
            data,
        })
    }

    /// Gets a reference to the data associated with this range.
    pub fn get(&self) -> &D {
        self.data
    }
}

impl<'a, D> Range for PayloadRange<'a, D> {
    fn min(&self) -> usize {
        self.range.min()
    }

    fn max(&self) -> usize {
        self.range.max()
    }

    fn min_incl(&self) -> usize {
        self.range.min_incl()
    }

    fn max_incl(&self) -> usize {
        self.range.max_incl()
    }

    fn includes(&self, value: usize) -> bool {
        self.range.includes(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[test]
    fn range_with_vec_payload() {
        let data = vec![1, 2, 3, 4, 5];
        let r = PayloadRange::new(10, 100, RangeMode::Inclusive, &data).unwrap();
        assert_eq!(r.get(), &data);
    }

    #[test]
    fn range_with_modifiable_payload() {
        let data = RefCell::new(vec![1, 2, 3, 4, 5]);
        let r = PayloadRange::new(10, 100, RangeMode::Inclusive, &data).unwrap();
        {
            let mut data_mut = r.get().borrow_mut();
            data_mut.push(6);
        }
        let data_ref = r.get().borrow();
        assert_eq!(data_ref.to_owned(), vec![1, 2, 3, 4, 5, 6]);
    }
}
