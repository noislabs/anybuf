use crate::varint::{to_zigzag32, to_zigzag64, unsigned_varint_encode};

/// The protobuf wire types
///
/// <https://protobuf.dev/programming-guides/encoding/#structure>
#[repr(u32)]
enum WireType {
    /// Variable length field (int32, int64, uint32, uint64, sint32, sint64, bool, enum)
    Varint = 0,
    // Fixed length types unsupported
    // I64 = 1,
    /// Lengths prefixed field (string, bytes, embedded messages, packed repeated fields)
    Len = 2,
    // group start/end (deprecated, unsupported)
    // SGROUP = 3,
    // EGROUP = 4,
    // Fixed length types unsupported
    // I32 = 5,
}

/// A minmal protobuf encoder.
#[derive(Default)]
pub struct Anybuf {
    output: Vec<u8>,
}

impl Anybuf {
    /// Creates a new serializer.
    ///
    /// See [`Anybuf::append_message`] for how to created nested messages using new Anybuf instances.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // Creates an empty document
    /// let serialized = Anybuf::new().into_vec();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Appends a bytes field with the given field number.
    pub fn append_bytes(mut self, field_number: u32, data: impl AsRef<[u8]>) -> Self {
        let data = data.as_ref();
        if data.is_empty() {
            return self;
        }
        // tag
        self.append_tag(field_number, WireType::Len);
        // length
        unsigned_varint_encode(data.len() as u64, &mut self.output);
        // value
        self.output.extend_from_slice(data);
        self
    }

    /// Appends a string field with the given field number.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // A string with field number 4 and 5
    /// let b = String::from("hello, world");
    /// let serialized = Anybuf::new()
    ///     .append_string(4, "nice content")
    ///     .append_string(5, b)
    ///     .into_vec();
    /// ```
    #[inline]
    pub fn append_string(self, field_number: u32, data: impl AsRef<str>) -> Self {
        self.append_bytes(field_number, data.as_ref().as_bytes())
    }

    /// Appends a uint64 field with the given field number.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // A uint64 with field number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_uint64(4, 3)
    ///     .append_uint64(5, u64::MAX)
    ///     .into_vec();
    /// ```
    pub fn append_uint64(mut self, field_number: u32, value: u64) -> Self {
        if value == 0 {
            return self;
        }
        self.append_tag(field_number, WireType::Varint);
        unsigned_varint_encode(value, &mut self.output);
        self
    }

    /// Appends a uint32 field with the given field number.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // A uint32 with field number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_uint32(4, 3)
    ///     .append_uint32(5, u32::MAX)
    ///     .into_vec();
    /// ```
    #[inline]
    pub fn append_uint32(self, field_number: u32, value: u32) -> Self {
        self.append_uint64(field_number, value.into())
    }

    /// Appends a bool field with the given field number.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // A boolean with field number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_bool(4, true)
    ///     .append_bool(5, false)
    ///     .into_vec();
    /// ```
    #[inline]
    pub fn append_bool(self, field_number: u32, value: bool) -> Self {
        self.append_uint64(field_number, value.into())
    }

    /// Appends an sint64 field with the given field number.
    ///
    /// Please note that protobuf has two different 64 bit signed integer types
    /// with different encodings: sint64 and int64. This only works for sint64.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // An sint64 with field number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_sint64(4, -700)
    ///     .append_sint64(5, i64::MAX)
    ///     .into_vec();
    /// ```
    pub fn append_sint64(self, field_number: u32, value: i64) -> Self {
        self.append_uint64(field_number, to_zigzag64(value))
    }

    /// Appends an sint32 field with the given field number.
    ///
    /// Please note that protobuf has two different 32 bit signed integer types
    /// with different encodings: sint32 and int32. This only works for sint32.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // An sint32 with field number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_sint32(4, -700)
    ///     .append_sint32(5, i32::MAX)
    ///     .into_vec();
    /// ```
    pub fn append_sint32(self, field_number: u32, value: i32) -> Self {
        self.append_uint32(field_number, to_zigzag32(value))
    }

    /// Appends an int64 field with the given field number.
    ///
    /// Please note that protobuf has two different 64 bit signed integer types
    /// with different encodings: sint64 and int64. This only works for the later.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // An int64 with field number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_int64(4, -700)
    ///     .append_int64(5, i64::MAX)
    ///     .into_vec();
    /// ```
    pub fn append_int64(self, field_number: u32, value: i64) -> Self {
        self.append_uint64(field_number, value as u64)
    }

    /// Appends an int32 field with the given field number.
    ///
    /// Please note that protobuf has two different 32 bit signed integer types
    /// with different encodings: sint32 and int32. This only works for the later.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // An int32 with field number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_int32(4, -700)
    ///     .append_int32(5, i32::MAX)
    ///     .into_vec();
    /// ```
    pub fn append_int32(self, field_number: u32, value: i32) -> Self {
        self.append_uint64(field_number, value as i64 as u64)
    }

    /// Appends a nested protobuf message with the given field number.
    pub fn append_message(self, field_number: u32, value: &Anybuf) -> Self {
        self.append_bytes(field_number, value.as_bytes())
    }

    /// Appends a repeated field of type uint32.
    ///
    /// Use this instead of multiple [`Anybuf::append_uint32`] to ensure 0 values are not lost.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // repeated uint32 fields with number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_repeated_uint32(4, &[0, 1, u32::MAX])
    ///     .append_repeated_uint32(5, &[])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_uint32(mut self, field_number: u32, data: &[u32]) -> Self {
        for value in data {
            self.append_tag(field_number, WireType::Varint);
            unsigned_varint_encode((*value).into(), &mut self.output);
        }
        self
    }

    /// Appends a repeated field of type uint64.
    ///
    /// Use this instead of multiple [`Anybuf::append_uint64`] to ensure 0 values are not lost.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // repeated uint64 fields with number 4 and 5
    /// let serialized = Anybuf::new()
    ///     .append_repeated_uint64(4, &[0, 1, u64::MAX])
    ///     .append_repeated_uint64(5, &[])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_uint64(mut self, field_number: u32, data: &[u64]) -> Self {
        for value in data {
            self.append_tag(field_number, WireType::Varint);
            unsigned_varint_encode(*value, &mut self.output);
        }
        self
    }

    /// Appends a repeated field of type sint32.
    ///
    /// Use this instead of multiple [`Anybuf::append_sint32`] to ensure 0 values are not lost.
    ///
    /// Please note that int32 and sint32 are two different signed integer types. This encodes
    /// only correctly for sint32.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // Three signed ints with field number 4
    /// let serialized = Anybuf::new()
    ///     .append_repeated_sint32(4, &[-30, 0, 17])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_sint32(mut self, field_number: u32, data: &[i32]) -> Self {
        for value in data {
            self.append_tag(field_number, WireType::Varint);
            unsigned_varint_encode(to_zigzag32(*value).into(), &mut self.output);
        }
        self
    }

    /// Appends a repeated field of type sint64.
    ///
    /// Use this instead of multiple [`Anybuf::append_sint64`] to ensure 0 values are not lost.
    ///
    /// Please note that int64 and sint64 are two different signed integer types. This encodes
    /// only correctly for sint64.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // Three signed ints with field number 4
    /// let serialized = Anybuf::new()
    ///     .append_repeated_sint64(4, &[-30, 0, 17])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_sint64(mut self, field_number: u32, data: &[i64]) -> Self {
        for value in data {
            self.append_tag(field_number, WireType::Varint);
            unsigned_varint_encode(to_zigzag64(*value), &mut self.output);
        }
        self
    }

    /// Appends a repeated field of type bool.
    ///
    /// Use this instead of multiple [`Anybuf::append_bool`] to ensure false values are not lost.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // Some booleans with field number 4
    /// let serialized = Anybuf::new()
    ///     .append_repeated_bool(4, &[true, false, true, true, false])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_bool(mut self, field_number: u32, data: &[bool]) -> Self {
        for value in data {
            self.append_tag(field_number, WireType::Varint);
            unsigned_varint_encode((*value).into(), &mut self.output);
        }
        self
    }

    /// Appends a repeated field of type int32.
    ///
    /// Use this instead of multiple [`Anybuf::append_int32`] to ensure 0 values are not lost.
    ///
    /// Please note that int32 and sint32 are two different signed integer types. This encodes
    /// only correctly for int32.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // Three signed ints with field number 4
    /// let serialized = Anybuf::new()
    ///     .append_repeated_sint32(4, &[-30, 0, 17])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_int32(mut self, field_number: u32, data: &[i32]) -> Self {
        for value in data {
            self.append_tag(field_number, WireType::Varint);
            unsigned_varint_encode(*value as i64 as u64, &mut self.output);
        }
        self
    }

    /// Appends a repeated field of type sint64.
    ///
    /// Use this instead of multiple [`Anybuf::append_sint64`] to ensure 0 values are not lost.
    ///
    /// Please note that int64 and sint64 are two different signed integer types. This encodes
    /// only correctly for int64.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // Three signed ints with field number 4
    /// let serialized = Anybuf::new()
    ///     .append_repeated_int64(4, &[-30, 0, 17])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_int64(mut self, field_number: u32, data: &[i64]) -> Self {
        for value in data {
            self.append_tag(field_number, WireType::Varint);
            unsigned_varint_encode(*value as u64, &mut self.output);
        }
        self
    }

    /// Appends a repeated field of type string.
    ///
    /// Use this instead of multiple [`Anybuf::append_string`] to ensure "" values are not lost.
    ///
    /// The generic type `S` is the type of a single element in the input slice. This
    /// is typically something like `&str` or `String`.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// let name = "Bono".to_string();
    ///
    /// // Three string fields with field number 4, slice of &str
    /// let serialized = Anybuf::new()
    ///     .append_repeated_string(4, &["", "Caro", &name])
    ///     .into_vec();
    ///
    /// // Works with String too
    /// let owned: Vec<String> = vec![
    ///     "green".to_string(),
    ///     "orange".to_string(),
    /// ];
    /// let serialized = Anybuf::new()
    ///     .append_repeated_string(4, &owned)
    ///     .into_vec();
    ///
    /// // Or array of constant values
    /// const A: &str = "Alice";
    /// const B: &str = "Bob";
    /// const ARRAY: [&str; 2] = [A, B];
    /// let serialized = Anybuf::new()
    ///     .append_repeated_string(4, &ARRAY)
    ///     .into_vec();
    /// ```
    pub fn append_repeated_string<S: AsRef<str>>(mut self, field_number: u32, data: &[S]) -> Self {
        for value in data {
            let value = value.as_ref();
            self.append_tag(field_number, WireType::Len);
            unsigned_varint_encode(value.len() as u64, &mut self.output);
            self.output.extend_from_slice(value.as_bytes());
        }
        self
    }

    /// Appends a repeated field of type bytes.
    ///
    /// Use this instead of multiple [`Anybuf::append_bytes`] to ensure empty values are not lost.
    ///
    /// The generic type `B` is the type of a single element in the input slice. This
    /// is typically something like `&[u8]`, `Vec<u8>` but also `&str` and `String` work.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// let blob = vec![4u8; 75];
    ///
    /// // Three bytes fields with field number 5, slice of slices
    /// let serialized = Anybuf::new()
    ///     .append_repeated_bytes(5, &[blob.as_slice(), b"", b"abcd"])
    ///     .into_vec();
    ///
    /// // Works with Vec<u8> elements too
    /// let owned: Vec<Vec<u8>> = vec![
    ///     vec![1u8; 10],
    ///     vec![2u8; 10],
    ///     vec![3u8; 10],
    /// ];
    /// let serialized = Anybuf::new()
    ///     .append_repeated_bytes(5, &owned)
    ///     .into_vec();
    ///
    /// // Or array of constant values
    /// const A: &[u8] = b"Alice";
    /// const B: &[u8] = b"Bob";
    /// const ARRAY: [&[u8]; 2] = [A, B];
    /// let serialized = Anybuf::new()
    ///     .append_repeated_bytes(5, &ARRAY)
    ///     .into_vec();
    /// ```
    pub fn append_repeated_bytes<B: AsRef<[u8]>>(mut self, field_number: u32, data: &[B]) -> Self {
        for value in data {
            let value = value.as_ref();
            // tag
            self.append_tag(field_number, WireType::Len);
            // length
            unsigned_varint_encode(value.len() as u64, &mut self.output);
            // value
            self.output.extend_from_slice(value);
        }
        self
    }

    /// Appends a repeated field of type message.
    ///
    /// Use this instead of multiple [`Anybuf::append_message`] to ensure empty values are not lost.
    ///
    /// The generic type `M` is the type of a single element in the input slice. This
    /// is typically `&Anybuf` or `Anybuf`.
    ///
    /// ## Example
    ///
    /// ```
    /// # use anybuf::Anybuf;
    /// // A repeated message at field number 11. This adds 3 elements, one of them is the default message.
    /// let serialized = Anybuf::new()
    ///     .append_repeated_message(11, &[
    ///         &Anybuf::new().append_uint32(1, 1),
    ///         &Anybuf::new(),
    ///         &Anybuf::new().append_uint32(1, 3),
    ///     ])
    ///     .into_vec();
    /// ```
    pub fn append_repeated_message<M: AsRef<Anybuf>>(
        mut self,
        field_number: u32,
        messages: &[M],
    ) -> Self {
        for message in messages {
            let data = message.as_ref().as_bytes();
            // tag
            self.append_tag(field_number, WireType::Len);
            // length
            unsigned_varint_encode(data.len() as u64, &mut self.output);
            // value
            self.output.extend_from_slice(data);
        }
        self
    }

    /// Returns the protobuf bytes of the instance.
    ///
    /// The data is the same as [`Anybuf::into_vec`] but does not consume the instance.
    pub fn as_bytes(&self) -> &[u8] {
        &self.output
    }

    /// Takes the instance and returns the protobuf bytes.
    ///
    /// The data is the same as [`Anybuf::as_bytes`] but consumes the instance in order to
    /// return an owned vector without cloning the data.
    pub fn into_vec(self) -> Vec<u8> {
        self.output
    }

    fn append_tag(&mut self, field_number: u32, field_type: WireType) {
        // The top 3 bits of a field number must be unset, ie.e this shift is safe for valid field numbers
        // "The smallest field number you can specify is 1, and the largest is 2^29-1, or 536,870,911"
        // https://protobuf.dev/programming-guides/proto3/#assigning-field-numbers
        let tag: u32 = (field_number << 3) | field_type as u32;
        unsigned_varint_encode(tag as u64, &mut self.output);
    }
}

impl AsRef<Anybuf> for Anybuf {
    #[inline]
    fn as_ref(&self) -> &Anybuf {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hex_literal::hex;

    #[test]
    fn new_returns_empty_data() {
        let data = Anybuf::new();
        assert_eq!(data.into_vec(), &[]);
    }

    #[test]
    fn append_uint64_works() {
        let data = Anybuf::new().append_uint64(1, 150);
        assert_eq!(data.into_vec(), [0b00001000, 0b10010110, 0b00000001]);

        // Zero/Default field not written
        let data = Anybuf::new().append_uint64(1, 0);
        assert_eq!(data.into_vec(), &[]);
    }

    #[test]
    fn append_uint32_works() {
        let data = Anybuf::new().append_uint32(1, 150);
        assert_eq!(data.into_vec(), [0b00001000, 0b10010110, 0b00000001]);

        // large value (echo "number: 215874321" | protoc --encode=Room *.proto | hexdump -C)
        let data = Anybuf::new().append_uint32(1, 215874321);
        assert_eq!(data.into_vec(), b"\x08\x91\xf6\xf7\x66");

        // max value (echo "number: 4294967295" | protoc --encode=Room *.proto | hexdump -C)
        let data = Anybuf::new().append_uint32(1, u32::MAX);
        assert_eq!(data.into_vec(), b"\x08\xff\xff\xff\xff\x0f");

        // Zero/Default field not written
        let data = Anybuf::new().append_uint32(1, 0);
        assert_eq!(data.into_vec(), &[]);
    }

    #[test]
    fn append_sint32_works() {
        // for x in -2147483648 -735983 -456 -2 -1 0 1 5 21 900 8247598 2147483647; do echo "$x,$(echo "altitude: $x" | protoc --encode=Room *.proto | xxd -p)"; done
        assert_eq!(
            Anybuf::new().append_sint32(4, -2147483648).into_vec(),
            hex!("20ffffffff0f")
        );
        assert_eq!(
            Anybuf::new().append_sint32(4, -735983).into_vec(),
            hex!("20ddeb59")
        );
        assert_eq!(
            Anybuf::new().append_sint32(4, -456).into_vec(),
            hex!("208f07")
        );
        assert_eq!(Anybuf::new().append_sint32(4, -2).into_vec(), hex!("2003"));
        assert_eq!(Anybuf::new().append_sint32(4, -1).into_vec(), hex!("2001"));
        assert_eq!(Anybuf::new().append_sint32(4, 0).into_vec(), hex!(""));
        assert_eq!(Anybuf::new().append_sint32(4, 1).into_vec(), hex!("2002"));
        assert_eq!(Anybuf::new().append_sint32(4, 5).into_vec(), hex!("200a"));
        assert_eq!(Anybuf::new().append_sint32(4, 21).into_vec(), hex!("202a"));
        assert_eq!(
            Anybuf::new().append_sint32(4, 900).into_vec(),
            hex!("20880e")
        );
        assert_eq!(
            Anybuf::new().append_sint32(4, 8247598).into_vec(),
            hex!("20dce4ee07")
        );
        assert_eq!(
            Anybuf::new().append_sint32(4, 2147483647).into_vec(),
            hex!("20feffffff0f")
        );
    }

    #[test]
    fn append_sint64_works() {
        // for x in -9223372036854775808 -2147483649 -2147483648 -735983 -456 -2 -1 0 1 5 21 900 8247598 2147483647 2147483648 9223372036854775807; do echo "$x,$(echo "temperature: $x" | protoc --encode=Room *.proto | xxd -p)"; done
        assert_eq!(
            Anybuf::new().append_sint64(5, i64::MIN).into_vec(),
            hex!("28ffffffffffffffffff01")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, -2147483649).into_vec(),
            hex!("288180808010")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, -2147483648).into_vec(),
            hex!("28ffffffff0f")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, -735983).into_vec(),
            hex!("28ddeb59")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, -456).into_vec(),
            hex!("288f07")
        );
        assert_eq!(Anybuf::new().append_sint64(5, -2).into_vec(), hex!("2803"));
        assert_eq!(Anybuf::new().append_sint64(5, -1).into_vec(), hex!("2801"));
        assert_eq!(Anybuf::new().append_sint64(5, 0).into_vec(), hex!(""));
        assert_eq!(Anybuf::new().append_sint64(5, 1).into_vec(), hex!("2802"));
        assert_eq!(Anybuf::new().append_sint64(5, 5).into_vec(), hex!("280a"));
        assert_eq!(Anybuf::new().append_sint64(5, 21).into_vec(), hex!("282a"));
        assert_eq!(
            Anybuf::new().append_sint64(5, 900).into_vec(),
            hex!("28880e")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, 8247598).into_vec(),
            hex!("28dce4ee07")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, 2147483647).into_vec(),
            hex!("28feffffff0f")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, 2147483648).into_vec(),
            hex!("288080808010")
        );
        assert_eq!(
            Anybuf::new().append_sint64(5, i64::MAX).into_vec(),
            hex!("28feffffffffffffffff01")
        );
    }

    #[test]
    fn append_int64_works() {
        // Example from https://protobuf.dev/programming-guides/encoding/#signed-ints
        let data = Anybuf::new().append_int64(1, -2);
        assert_eq!(
            data.into_vec(),
            [
                0b00001000, 0b11111110, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111, 0b11111111, 0b11111111, 0b00000001
            ]
        );

        // for x in -9223372036854775808 -2147483649 -2147483648 -735983 -456 -2 -1 0 1 5 21 900 8247598 2147483647 2147483648 9223372036854775807; do echo "($x,hex!(\"$(echo "humidity: $x" | protoc --encode=Room *.proto | xxd -p)\").as_slice()),"; done
        let tests: [(i64, &[u8]); 16] = [
            (
                -9223372036854775808,
                hex!("3080808080808080808001").as_slice(),
            ),
            (-2147483649, hex!("30fffffffff7ffffffff01").as_slice()),
            (-2147483648, hex!("3080808080f8ffffffff01").as_slice()),
            (-735983, hex!("30918ad3ffffffffffff01").as_slice()),
            (-456, hex!("30b8fcffffffffffffff01").as_slice()),
            (-2, hex!("30feffffffffffffffff01").as_slice()),
            (-1, hex!("30ffffffffffffffffff01").as_slice()),
            (0, hex!("").as_slice()),
            (1, hex!("3001").as_slice()),
            (5, hex!("3005").as_slice()),
            (21, hex!("3015").as_slice()),
            (900, hex!("308407").as_slice()),
            (8247598, hex!("30aeb2f703").as_slice()),
            (2147483647, hex!("30ffffffff07").as_slice()),
            (2147483648, hex!("308080808008").as_slice()),
            (9223372036854775807, hex!("30ffffffffffffffff7f").as_slice()),
        ];
        for (value, expected) in tests {
            let data = Anybuf::new().append_int64(6, value);
            assert_eq!(data.into_vec(), expected, "Errored for value: {value}");
        }
    }

    #[test]
    fn append_int32_works() {
        // For values >= 0, int32 and uint32 encoding is the same
        // https://github.com/protocolbuffers/protobuf/blob/v24.4/java/core/src/main/java/com/google/protobuf/BinaryWriter.java#L1114-L1115
        for x in [0, 1, 4, 70, 8979879, i32::MAX] {
            let a = Anybuf::new().append_int32(1, x).into_vec();
            let b = Anybuf::new().append_uint32(1, x as u32).into_vec();
            assert_eq!(a, b);
        }

        // for x in -2147483648 -735983 -456 -2 -1 0 1 5 21 900 8247598 2147483647; do echo "($x,hex!(\"$(echo "pressure: $x" | protoc --encode=Room *.proto | xxd -p)\").as_slice()),"; done
        let tests: [(i32, &[u8]); 12] = [
            (-2147483648, hex!("3880808080f8ffffffff01").as_slice()),
            (-735983, hex!("38918ad3ffffffffffff01").as_slice()),
            (-456, hex!("38b8fcffffffffffffff01").as_slice()),
            (-2, hex!("38feffffffffffffffff01").as_slice()),
            (-1, hex!("38ffffffffffffffffff01").as_slice()),
            (0, hex!("").as_slice()),
            (1, hex!("3801").as_slice()),
            (5, hex!("3805").as_slice()),
            (21, hex!("3815").as_slice()),
            (900, hex!("388407").as_slice()),
            (8247598, hex!("38aeb2f703").as_slice()),
            (2147483647, hex!("38ffffffff07").as_slice()),
        ];
        for (value, expected) in tests {
            let data = Anybuf::new().append_int32(7, value);
            assert_eq!(data.into_vec(), expected, "Errored for value: {value}");
        }
    }

    #[test]
    fn append_bool_works() {
        // echo "on: true" | protoc --encode=Lights *.proto | hexdump -C
        let data = Anybuf::new().append_bool(3, true);
        assert_eq!(data.into_vec(), [0x18, 0x01]);

        // Zero/Default field not written
        let data = Anybuf::new().append_bool(3, false);
        assert_eq!(data.into_vec(), &[]);
    }

    #[test]
    fn append_bytes() {
        // &str
        let data = Anybuf::new().append_bytes(2, "testing");
        assert_eq!(
            data.into_vec(),
            [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]
        );

        // String
        let data = Anybuf::new().append_bytes(2, String::from("testing"));
        assert_eq!(
            data.into_vec(),
            [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]
        );

        // &[u8]
        let data = Anybuf::new().append_bytes(2, b"testing");
        assert_eq!(
            data.into_vec(),
            [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]
        );

        // Empty field not written
        let data = Anybuf::new().append_bytes(2, b"");
        assert_eq!(data.into_vec(), []);
    }

    #[test]
    fn append_string() {
        // &str
        let data = Anybuf::new().append_string(2, "testing");
        assert_eq!(
            data.into_vec(),
            [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]
        );

        // String
        let data = Anybuf::new().append_string(2, String::from("testing"));
        assert_eq!(
            data.into_vec(),
            [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]
        );

        // Empty field not written
        let data = Anybuf::new().append_string(2, "");
        assert_eq!(data.into_vec(), []);
    }

    #[test]
    fn append_message_works() {
        // echo "number: 4; lights: {on: true}; size: 56" | protoc --encode=Room *.proto | hexdump -C
        let data = Anybuf::new()
            .append_uint64(1, 4)
            .append_message(2, &Anybuf::new().append_bool(3, true))
            .append_uint64(3, 56);
        assert_eq!(data.into_vec(), b"\x08\x04\x12\x02\x18\x01\x18\x38");
    }

    #[test]
    fn append_repeated_uint32_works() {
        // echo "id: \"uint32s\"; numbers_uint32: [0, 1, 2, 37546, 4294967295]" | protoc --encode=Collection *.proto | xxd -p
        let data = Anybuf::new()
            .append_string(1, "uint32s")
            .append_repeated_uint32(2, &[0, 1, 2, 37546, 4294967295]);
        assert_eq!(
            data.into_vec(),
            hex!("0a0775696e7433327310001001100210aaa50210ffffffff0f")
        );

        // echo "id: \"no uint32s\"; numbers_uint32: []" | protoc --encode=Collection *.proto | xxd -p
        let data = Anybuf::new()
            .append_string(1, "no uint32s")
            .append_repeated_uint32(2, &[]);
        assert_eq!(data.into_vec(), hex!("0a0a6e6f2075696e74333273"));
    }

    #[test]
    fn append_repeated_uint64_works() {
        // echo "id: \"uint64s\"; numbers_uint64: [0, 1, 2, 37546, 4294967295, 18446744073709551615]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "uint64s")
            .append_repeated_uint64(3, &[0, 1, 2, 37546, 4294967295, u64::MAX]);
        assert_eq!(
            data.into_vec(),
            hex!("0a0775696e7436347318001801180218aaa50218ffffffff0f18ffffffffffffffffff01")
        );

        // echo "id: \"no uint64s\"; numbers_uint64: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no uint64s")
            .append_repeated_uint64(3, &[]);
        assert_eq!(data.into_vec(), hex!("0a0a6e6f2075696e74363473"));
    }

    #[test]
    fn append_repeated_sint32_works() {
        // echo "id: \"sint32s\"; numbers_sint32: [-2147483648, -1, 0, 1, 2, 37546, 2147483647]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "sint32s")
            .append_repeated_sint32(4, &[i32::MIN, -1, 0, 1, 2, 37546, i32::MAX]);
        assert_eq!(
            data.into_vec(),
            hex!("0a0773696e7433327320ffffffff0f200120002002200420d4ca0420feffffff0f")
        );

        // echo "id: \"no sint32s\"; numbers_sint32: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no sint32s")
            .append_repeated_sint32(4, &[]);
        assert_eq!(data.into_vec(), hex!("0a0a6e6f2073696e74333273"));
    }

    #[test]
    fn append_repeated_sint64_works() {
        // echo "id: \"sint64s\"; numbers_sint64: [-9223372036854775808, -1, 0, 1, 2, 37546, 4294967295, 9223372036854775807]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "sint64s")
            .append_repeated_sint64(5, &[i64::MIN, -1, 0, 1, 2, 37546, 4294967295, i64::MAX]);
        assert_eq!(
            data.into_vec(),
            hex!("0a0773696e7436347328ffffffffffffffffff01280128002802280428d4ca0428feffffff1f28feffffffffffffffff01")
        );

        // echo "id: \"no sint64s\"; numbers_sint64: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no sint64s")
            .append_repeated_uint64(5, &[]);
        assert_eq!(data.into_vec(), hex!("0a0a6e6f2073696e74363473"));
    }

    #[test]
    fn append_repeated_bool_works() {
        // echo "id: \"bools\"; booleans: [false, false, true, true, false]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "bools")
            .append_repeated_bool(8, &[false, false, true, true, false]);
        assert_eq!(data.into_vec(), hex!("0a05626f6f6c7340004000400140014000"));

        // echo "id: \"no bools\"; booleans: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no bools")
            .append_repeated_uint64(8, &[]);
        assert_eq!(data.into_vec(), hex!("0a086e6f20626f6f6c73"));
    }

    #[test]
    fn append_repeated_int32_works() {
        // echo "id: \"int32s\"; numbers_int32: [-2147483648, -1, 0, 1, 2, 37546, 2147483647]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "int32s")
            .append_repeated_int32(6, &[i32::MIN, -1, 0, 1, 2, 37546, i32::MAX]);
        assert_eq!(
            data.into_vec(),
            hex!("0a06696e743332733080808080f8ffffffff0130ffffffffffffffffff0130003001300230aaa50230ffffffff07")
        );

        // echo "id: \"no int32s\"; numbers_int32: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no int32s")
            .append_repeated_int32(6, &[]);
        assert_eq!(data.into_vec(), hex!("0a096e6f20696e74333273"));
    }

    #[test]
    fn append_repeated_int64_works() {
        // echo "id: \"int64s\"; numbers_int64: [-9223372036854775808, -1, 0, 1, 2, 37546, 4294967295, 9223372036854775807]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "int64s")
            .append_repeated_int64(7, &[i64::MIN, -1, 0, 1, 2, 37546, 4294967295, i64::MAX]);
        assert_eq!(
            data.into_vec(),
            hex!("0a06696e74363473388080808080808080800138ffffffffffffffffff0138003801380238aaa50238ffffffff0f38ffffffffffffffff7f")
        );

        // echo "id: \"no int64s\"; numbers_int64: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no int64s")
            .append_repeated_int64(7, &[]);
        assert_eq!(data.into_vec(), hex!("0a096e6f20696e74363473"));
    }

    #[test]
    fn append_repeated_string_works() {
        // echo "id: \"strings\"; strings: [\"\", \"a\", \"bcde\"]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "strings")
            .append_repeated_string(9, &["", "a", "bcde"]);
        assert_eq!(
            data.into_vec(),
            hex!("0a07737472696e67734a004a01614a0462636465")
        );

        // echo "id: \"no strings\"; strings: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no strings")
            .append_repeated_string::<&str>(9, &[]);
        assert_eq!(data.into_vec(), hex!("0a0a6e6f20737472696e6773"));

        // vector of Strings
        // echo "id: \"strings\"; strings: [\"a\", \"b\", \"c\"]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let owned = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let data = Anybuf::new()
            .append_string(1, "strings")
            .append_repeated_string(9, &owned);
        assert_eq!(
            data.into_vec(),
            hex!("0a07737472696e67734a01614a01624a0163")
        );
    }

    #[test]
    fn append_repeated_bytes_works() {
        // echo "id: \"bytess\"; bytess: [\"\", \"a\", \"bcde\"]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "bytess")
            .append_repeated_bytes::<&[u8]>(10, &[b"", b"a", b"bcde"]);
        assert_eq!(
            data.into_vec(),
            hex!("0a066279746573735200520161520462636465")
        );

        // echo "id: \"no bytess\"; bytess: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no bytess")
            .append_repeated_bytes::<&[u8]>(10, &[]);
        assert_eq!(data.into_vec(), hex!("0a096e6f20627974657373"));

        // vector of bytes
        // echo "id: \"bytess\"; bytess: [\"c\", \"b\", \"a\"]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let owned = vec![
            "c".to_string().into_bytes(),
            "b".to_string().into_bytes(),
            "a".to_string().into_bytes(),
        ];
        let data = Anybuf::new()
            .append_string(1, "bytess")
            .append_repeated_bytes(10, &owned);
        assert_eq!(data.into_vec(), hex!("0a06627974657373520163520162520161"));
    }

    #[test]
    fn append_repeated_message_works() {
        // echo "messages: [{ number: 1}, { number: 2}, { number: 3}]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new().append_repeated_message(
            11,
            &[
                &Anybuf::new().append_uint32(1, 1),
                &Anybuf::new().append_uint32(1, 2),
                &Anybuf::new().append_uint32(1, 3),
            ],
        );
        assert_eq!(data.into_vec(), hex!("5a0208015a0208025a020803"));

        // An empty message
        // echo "messages: [{ number: 1}, { }, { number: 3}]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new().append_repeated_message(
            11,
            &[
                &Anybuf::new().append_uint32(1, 1),
                &Anybuf::new(),
                &Anybuf::new().append_uint32(1, 3),
            ],
        );
        assert_eq!(data.into_vec(), hex!("5a0208015a005a020803"));

        // echo "id: \"no messages\"; messages: []" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new()
            .append_string(1, "no messages")
            .append_repeated_message::<&Anybuf>(11, &[]);
        assert_eq!(data.into_vec(), hex!("0a0b6e6f206d65737361676573"));

        // Works for owned Anybuf instances. We can't easily create a Vec<&Anybuf> because the references outlive the instances.
        let owned: Vec<Anybuf> = vec![
            Anybuf::new().append_uint32(1, 1),
            Anybuf::new().append_uint32(1, 2),
            Anybuf::new().append_uint32(1, 3),
        ];
        // echo "messages: [{ number: 1}, { number: 2}, { number: 3}]" | protoc --encode=Collection *.proto | xxd -p -c 9999
        let data = Anybuf::new().append_repeated_message(11, &owned);
        assert_eq!(data.into_vec(), hex!("5a0208015a0208025a020803"));
    }
}
