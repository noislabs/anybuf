use std::collections::HashMap;

use crate::slice_reader::SliceReader;

/// A minmal protobuf decoder.
///
/// Decodes protobuf bytes and allows you to access the field.
///
/// The decoding step is zero-copy for variable length values, i.e.
/// no heap allocations are done for bytes and string fields as long as you do not access them.
/// The accessors then copy the values you need.
///
/// ## Example
///
/// ```
/// use anybuf::{Anybuf, Bufany};
///
/// let serialized: Vec<u8> = Anybuf::new()
///     .append_uint64(1, 150)
///     .append_uint32(2, 38)
///     .append_bytes(3, vec![0xF0, 0x00])
///     .append_string(4, "valid utf8 string")
///     .into_vec();
/// let decoded = Bufany::deserialize(&serialized).unwrap();
/// assert_eq!(decoded.uint64(1), Some(150));
/// assert_eq!(decoded.uint32(2), Some(38));
/// assert_eq!(decoded.bytes(3), Some(vec![0xF0, 0x00]));
/// assert_eq!(decoded.string(4), Some("valid utf8 string".to_string()));
/// assert_eq!(decoded.string(5), None);
/// ```
#[derive(Debug)]
pub struct Bufany<'a> {
    // A map from field number to decoded value.
    fields: HashMap<u32, Vec<Value<'a>>>,
}

#[derive(Debug)]
pub enum BufanyError {
    /// Found tag that is either not valid protobuf or unsuppored
    InvalidTag,
    /// Field number must be between 1 and 536,870,911
    InvalidFieldNumber,
    UnsupportedWireType(u8),
    ErrorDecodingVarint,
    /// The remaining data is not long enough to read the expected length
    UnexpectedEndOfData,
    Other,
}

impl<'a> Bufany<'a> {
    /// Creates a new serializer.
    pub fn deserialize(serialized: &'a [u8]) -> Result<Bufany<'a>, BufanyError> {
        let mut out: Bufany<'a> = Bufany {
            fields: Default::default(),
        };

        let mut reader = SliceReader::new(serialized);

        loop {
            if reader.is_empty() {
                break;
            }

            let Some(tag) = read_unsigned_varint(&mut reader) else {
                return Err(BufanyError::InvalidTag);
            };

            // valid field numbers are between 1 and 536,870,911
            let field_number: u32 = (tag >> 3)
                .try_into()
                .map_err(|_| BufanyError::InvalidFieldNumber)?;
            let wire_type = (tag & 0x07) as u8;

            let value = read_value(&mut reader, wire_type)?;
            out.fields.entry(field_number).or_default().push(value);
        }

        Ok(out)
    }

    /// Gets bytes from the given field number. This returns None if
    /// - the field number does not exist
    /// - the value type is not variable length
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_uint64(1, 150)
    ///     .append_bytes(2, vec![0xF0, 0x00])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.bytes(1), None);
    /// assert_eq!(decoded.bytes(2), Some(vec![0xF0, 0x00]));
    /// ```
    pub fn bytes(&self, field_number: u32) -> Option<Vec<u8>> {
        match self.value_ref(field_number) {
            Some(Value::VariableLength(data)) => Some(data.to_vec()),
            _ => None,
        }
    }

    /// Gets bytes from the given field number. This returns None if
    /// - the field number does not exist
    /// - the value type is not variable length
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_uint64(1, 150)
    ///     .append_bytes(2, vec![0xF0, 0x00])
    ///     .append_string(3, "valid utf8 string")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.string(1), None);
    /// assert_eq!(decoded.string(2), None);
    /// assert_eq!(decoded.string(3), Some("valid utf8 string".to_string()));
    /// ```
    pub fn string(&self, field_number: u32) -> Option<String> {
        let bytes = self.bytes(field_number)?;
        String::from_utf8(bytes).ok()
    }

    /// Gets a uint64 from the given field number. This returns None if
    /// - the field number does not exist
    /// - the value type is not of type varint
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_uint64(1, 150)
    ///     .append_bytes(2, vec![0xF0, 0x00])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.uint64(1), Some(150));
    /// assert_eq!(decoded.uint64(2), None);
    /// assert_eq!(decoded.uint64(3), None);
    /// ```
    pub fn uint64(&self, field_number: u32) -> Option<u64> {
        match self.value_ref(field_number) {
            Some(Value::Varint(data)) => Some(*data),
            _ => None,
        }
    }

    /// Gets a uint32 from the given field number. This returns None if
    /// - the field number does not exist
    /// - the value type is not of type varint
    /// - the value value exceeds the uint32 range
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_uint32(1, 150)
    ///     .append_uint64(2, 17)
    ///     .append_uint64(3, 36028797018963970)
    ///     .append_bytes(3, vec![0xF0, 0x00])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.uint32(1), Some(150));
    /// assert_eq!(decoded.uint32(2), Some(17)); // works because on the wire we don't differentiate
    /// assert_eq!(decoded.uint32(3), None); // too large
    /// assert_eq!(decoded.uint32(4), None);
    /// ```
    pub fn uint32(&self, field_number: u32) -> Option<u32> {
        match self.value_ref(field_number) {
            Some(Value::Varint(data)) => (*data).try_into().ok(),
            _ => None,
        }
    }

    /// Gets the value of the given field number. This returns None if
    /// the field number does not exist
    pub fn value(&self, field_number: u32) -> Option<Value> {
        self.value_ref(field_number).cloned()
    }

    /// Gets the first value of the given field number as a reference.
    /// This returns None if the field number does not exist
    fn value_ref(&self, field_number: u32) -> Option<&Value<'_>> {
        match self.fields.get(&field_number) {
            Some(field) => field.first(),
            None => None,
        }
    }
}

fn read_unsigned_varint(data: &mut SliceReader) -> Option<u64> {
    let mut out = 0u64;
    let mut byte_counter = 0;
    loop {
        let Some(byte) = data.read_one() else {
            return None;
        };
        let value = (byte & 0x7f) as u64;
        out += value << (byte_counter * 7);

        byte_counter += 1;
        if byte & 0x80 == 0 {
            break;
        }
    }

    Some(out)
}

/// A deserialized value
#[derive(Debug, PartialEq, Clone)]
pub enum Value<'a> {
    /// Unknown varint (wire type = 0).
    Varint(u64),

    /// A 64-bit value (wire type = 1). Used for fixed64, sfixed64, double.
    I64([u8; 8]),

    /// Unknown variable length value (wire type = 2).
    VariableLength(&'a [u8]),

    /// A 32-bit value (wire type = 5). Used for fixed32, sfixed32, float.
    I32([u8; 4]),
}

impl PartialEq<Value<'_>> for &Value<'_> {
    fn eq(&self, rhs: &Value) -> bool {
        *self == rhs
    }
}

impl PartialEq<&Value<'_>> for Value<'_> {
    fn eq(&self, rhs: &&Value) -> bool {
        self == *rhs
    }
}

fn read_value<'a>(data: &mut SliceReader<'a>, wire_type: u8) -> Result<Value<'a>, BufanyError> {
    let value = match wire_type {
        0 => Value::Varint(read_unsigned_varint(data).ok_or(BufanyError::ErrorDecodingVarint)?),
        1 => Value::I64(
            data.read_array::<8>()
                .ok_or(BufanyError::UnexpectedEndOfData)?,
        ),
        2 => {
            let length = read_unsigned_varint(data).ok_or(BufanyError::ErrorDecodingVarint)?;
            let length = length as usize; // Is this safe?
            let Some(consumed) = data.read(length) else {
                return Err(BufanyError::UnexpectedEndOfData);
            };
            Value::VariableLength(consumed)
        }
        // group start/end (deprecated, unsupported)
        // SGROUP = 3,
        // EGROUP = 4,
        5 => Value::I32(
            data.read_array::<4>()
                .ok_or(BufanyError::UnexpectedEndOfData)?,
        ),
        _ => return Err(BufanyError::UnsupportedWireType(wire_type)),
    };
    Ok(value)
}

#[cfg(test)]
mod tests {
    use crate::Anybuf;

    use super::*;

    #[test]
    fn deserialize_works() {
        // no field
        let serialized = Anybuf::new().into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 0);

        // one field
        let serialized = Anybuf::new().append_uint64(1, 150).into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 1);
        assert_eq!(decoded.fields.get(&1).unwrap(), &[Value::Varint(150)]);

        // two fields
        let serialized = Anybuf::new()
            .append_uint64(1, 150)
            .append_uint64(2, 42)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 2);
        assert_eq!(decoded.fields.get(&1).unwrap(), &[Value::Varint(150)]);
        assert_eq!(decoded.fields.get(&2).unwrap(), &[Value::Varint(42)]);

        // two fields out of order
        let serialized = Anybuf::new()
            .append_uint64(2, 42)
            .append_uint64(1, 150)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 2);
        assert_eq!(decoded.fields.get(&1).unwrap(), &[Value::Varint(150)]);
        assert_eq!(decoded.fields.get(&2).unwrap(), &[Value::Varint(42)]);

        // two fields of the same number
        let serialized = Anybuf::new()
            .append_uint64(7, 42)
            .append_uint64(7, 150)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 1);
        assert_eq!(
            decoded.fields.get(&7).unwrap(),
            &[Value::Varint(42), Value::Varint(150)]
        );

        // A single variable length field
        let serialized = [10, 4, 116, 114, 117, 101];
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 1);
        assert_eq!(
            decoded.fields.get(&1).unwrap(),
            &[Value::VariableLength(&[116, 114, 117, 101])]
        );
    }

    #[test]
    fn deserialize_repeated_works() {
        // An uint64 list in field number 7
        let serialized = Anybuf::new()
            .append_uint64(7, 150)
            .append_uint64(7, 42)
            .append_uint64(7, 1)
            .append_uint64(7, 0xFFFFFFFFFFFFFFFF)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 1);
        assert_eq!(
            decoded.fields.get(&7).unwrap(),
            &[
                Value::Varint(150),
                Value::Varint(42),
                Value::Varint(1),
                Value::Varint(0xFFFFFFFFFFFFFFFF)
            ]
        );
    }

    #[test]
    fn deserialize_handles_errors() {
        // length (5) loger than remaining data (5)
        let serialized = [10, 5, 116, 114, 117, 101];
        let err = Bufany::deserialize(&serialized).unwrap_err();
        match err {
            BufanyError::UnexpectedEndOfData => {}
            err => panic!("Unexpected error: {err:?}"),
        }

        // length (3) shorter than remaining data (4), i.e. we have one garbage byte at the end
        let serialized = [10, 3, 116, 114, 117, 101];
        let err = Bufany::deserialize(&serialized).unwrap_err();
        match err {
            BufanyError::UnexpectedEndOfData => {}
            err => panic!("Unexpected error: {err:?}"),
        }

        // First byte is not a valid tag (must be a varint)
        let serialized = [130];
        let err = Bufany::deserialize(&serialized).unwrap_err();
        match err {
            BufanyError::InvalidTag => {}
            err => panic!("Unexpected error: {err:?}"),
        }
    }

    #[test]
    fn get_bytes_works() {
        let serialized = Anybuf::new()
            .append_uint64(1, 150)
            .append_bytes(2, vec![0xF0, 0x00])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.bytes(1), None);
        assert_eq!(decoded.bytes(2), Some(vec![0xF0, 0x00]));
    }

    #[test]
    fn read_fixed_length_works() {
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

    #[test]
    fn read_unsigned_varint_works() {
        // tests from https://codeberg.org/ft/ufw/src/tag/v4.1.0/test/t-varint.c#L92-L101
        {
            let original = vec![0u8];
            let mut reader = SliceReader::new(&original);
            assert_eq!(read_unsigned_varint(&mut reader).unwrap(), 0);
            assert_eq!(reader.len(), 0);

            let original = vec![0x80, 0x01];
            let mut reader = SliceReader::new(&original);
            assert_eq!(read_unsigned_varint(&mut reader).unwrap(), 128);
            assert_eq!(reader.len(), 0);

            let original = vec![0xd2, 0x09];
            let mut reader = SliceReader::new(&original);
            assert_eq!(read_unsigned_varint(&mut reader).unwrap(), 1234);
            assert_eq!(reader.len(), 0);

            let original = vec![0xff, 0xff, 0xff, 0xff, 0x0f];
            let mut reader = SliceReader::new(&original);
            assert_eq!(read_unsigned_varint(&mut reader).unwrap(), u32::MAX as u64);
            assert_eq!(reader.len(), 0);
        }

        // examples from https://github.com/multiformats/unsigned-varint
        {
            // two different representations of the same value
            let mut reader = SliceReader::new(&[0x81, 0x00]);
            assert_eq!(read_unsigned_varint(&mut reader).unwrap(), 1);
            let mut reader = SliceReader::new(&[0x1]);
            assert_eq!(read_unsigned_varint(&mut reader).unwrap(), 1);

            for (expected, data) in [
                (1, vec![0x01]),
                (127, vec![0x7f]),
                (128, vec![0x80, 0x01]),
                (255, vec![0xff, 0x01]),
                (300, vec![0xac, 0x02]),
                (16384, vec![0x80, 0x80, 0x01]),
            ] {
                let mut reader = SliceReader::new(&data);
                assert_eq!(read_unsigned_varint(&mut reader).unwrap(), expected);
            }
        }
    }
}
