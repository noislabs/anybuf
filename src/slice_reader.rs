/// A mutable reader of an immutable data source
pub struct SliceReader<'x> {
    data: &'x [u8],
    pos: usize,
}

impl<'x> SliceReader<'x> {
    pub fn new(data: &'x [u8]) -> Self {
        Self { data, pos: 0 }
    }

    pub fn is_empty(&self) -> bool {
        self.pos == self.data.len()
    }

    /// Remaining data to read
    pub fn len(&self) -> usize {
        self.data.len() - self.pos
    }

    /// Advances the position by `n`.
    /// Note that advancing beyond the end of the data source is illegal and undefined behaviour.
    fn advance_by(&mut self, n: usize) {
        self.pos += n;
        debug_assert!(self.pos <= self.data.len())
    }

    /// Reads `n` bytes and advances the reader by `n`
    pub fn read(&mut self, n: usize) -> Option<&'x [u8]> {
        // Use https://doc.rust-lang.org/std/primitive.slice.html#method.split_array_mut once stable
        if self.len() < n {
            return None;
        }
        let out = &self.data[self.pos..self.pos + n];
        self.advance_by(n);
        Some(out)
    }

    /// Reads one byte and advances the reader by 1
    pub fn read_one(&mut self) -> Option<u8> {
        if self.len() < 1 {
            return None;
        }
        let out = self.data[self.pos];
        self.advance_by(1);
        Some(out)
    }

    /// Reads `N` bytes and advances the reader by `N`.
    /// The result is copied into an array
    pub fn read_array<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.read(N).map(|consumed| consumed.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_array_works() {
        let original = vec![5u8, 7, 234, 2, 45, 0, 12, 32, 192];

        // read 3
        let mut reader = SliceReader::new(&original);
        assert_eq!(reader.read_array::<3>().unwrap(), [5, 7, 234]);
        assert_eq!(reader.len(), 6);

        // read 2
        let mut reader = SliceReader::new(&original);
        assert_eq!(reader.read_array::<2>().unwrap(), [5, 7]);
        assert_eq!(reader.len(), 7);

        // read 1
        let mut reader = SliceReader::new(&original);
        assert_eq!(reader.read_array::<1>().unwrap(), [5]);
        assert_eq!(reader.len(), 8);

        // read 0
        let mut reader = SliceReader::new(&original);
        assert_eq!(reader.read_array::<0>().unwrap(), []);
        assert_eq!(reader.len(), 9);

        // read 10 (exceeds length)
        let mut reader = SliceReader::new(&original);
        assert!(reader.read_array::<10>().is_none());
        assert_eq!(reader.len(), 9);

        // consecutive reads (2, 3, 4 bytes)
        let mut reader = SliceReader::new(&original);
        assert_eq!(reader.read_array::<2>().unwrap(), [5, 7]);
        assert_eq!(reader.read_array::<3>().unwrap(), [234, 2, 45]);
        assert_eq!(reader.read_array::<4>().unwrap(), [0, 12, 32, 192]);
        assert_eq!(reader.len(), 0);
    }
}
