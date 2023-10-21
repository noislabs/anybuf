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
