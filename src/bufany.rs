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
/// assert_eq!(decoded.string(5), Some("".to_string()));
/// ```
#[derive(Debug)]
pub struct Bufany<'a> {
    // A map from field number to decoded value.
    fields: HashMap<u32, Vec<Value<'a>>>,
    // A vector that is always empty and has the lifetime we need.
    empty_vec: Vec<Value<'a>>,
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

#[derive(Debug)]
pub enum RepeatedError {
    /// Found a value of the wrong wire type
    TypeMismatch,
    /// A variable length field did not contain valid UTF-8.
    InvalidUtf8,
}

impl<'a> Bufany<'a> {
    /// Creates a new serializer.
    pub fn deserialize(serialized: &'a [u8]) -> Result<Bufany<'a>, BufanyError> {
        let mut out: Bufany<'a> = Bufany {
            fields: Default::default(),
            empty_vec: Default::default(),
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
    ///     .append_bytes(3, vec![])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.bytes(1), None); // wrong type
    /// assert_eq!(decoded.bytes(2), Some(vec![0xF0, 0x00]));
    /// assert_eq!(decoded.bytes(3), Some(vec![])); // not serialized => default
    /// assert_eq!(decoded.bytes(4), Some(vec![])); // not serialized => default
    /// ```
    pub fn bytes(&self, field_number: u32) -> Option<Vec<u8>> {
        match self.value_ref(field_number) {
            Some(Value::VariableLength(data)) => Some(data.to_vec()),
            Some(_) => None, // wrong type
            None => Some(Vec::new()),
        }
    }

    /// Gets bytes from the given field number. This returns None if
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
    ///     .append_string(4, "")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.string(1), None); // wrong type
    /// assert_eq!(decoded.string(2), None); // invalid utf8
    /// assert_eq!(decoded.string(3), Some("valid utf8 string".to_string()));
    /// assert_eq!(decoded.string(4), Some("".to_string())); // not serialized => default
    /// assert_eq!(decoded.string(5), Some("".to_string())); // not serialized => default
    /// ```
    pub fn string(&self, field_number: u32) -> Option<String> {
        let bytes = self.bytes(field_number)?;
        String::from_utf8(bytes).ok()
    }

    /// Gets a uint64 from the given field number. This returns None if
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
    ///     .append_uint64(3, 0)
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.uint64(1), Some(150));
    /// assert_eq!(decoded.uint64(2), None);
    /// assert_eq!(decoded.uint64(3), Some(0));
    /// assert_eq!(decoded.uint64(4), Some(0));
    /// ```
    pub fn uint64(&self, field_number: u32) -> Option<u64> {
        match self.value_ref(field_number) {
            Some(Value::Varint(data)) => Some(*data),
            Some(_) => None, // found but wrong type
            None => Some(0), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets a uint32 from the given field number. This returns None if
    /// - the value type is not of type varint
    /// - the value exceeds the uint32 range
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
    ///     .append_bytes(4, vec![0xF0, 0x00])
    ///     .append_uint32(5, 0)
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.uint32(1), Some(150));
    /// assert_eq!(decoded.uint32(2), Some(17)); // works because on the wire we don't differentiate
    /// assert_eq!(decoded.uint32(3), None); // too large
    /// assert_eq!(decoded.uint32(4), None);
    /// assert_eq!(decoded.uint32(5), Some(0));
    /// ```
    pub fn uint32(&self, field_number: u32) -> Option<u32> {
        match self.value_ref(field_number) {
            Some(Value::Varint(data)) => (*data).try_into().ok(),
            Some(_) => None, // found but wrong type
            None => Some(0), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets a bool from the given field number. This returns None if
    /// - the value type is not of type varint
    /// - the value is not 0 or 1 range
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_uint32(1, 150)
    ///     .append_uint64(2, 17)
    ///     .append_uint64(3, 1)
    ///     .append_bytes(4, vec![0xF0, 0x00])
    ///     .append_bool(5, true)
    ///     .append_bool(6, false)
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.bool(1), None); // too large
    /// assert_eq!(decoded.bool(2), None); // too large
    /// assert_eq!(decoded.bool(3), Some(true)); // 1 and true cannot be differentiated
    /// assert_eq!(decoded.bool(4), None); // wrong type
    /// assert_eq!(decoded.bool(5), Some(true));
    /// assert_eq!(decoded.bool(6), Some(false));
    /// ```
    pub fn bool(&self, field_number: u32) -> Option<bool> {
        match self.value_ref(field_number) {
            Some(Value::Varint(1)) => Some(true),
            Some(Value::Varint(0)) => Some(false),
            Some(Value::Varint(_)) => None,
            Some(_) => None,     // found but wrong type
            None => Some(false), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets repeated string from the given field number.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_uint64(1, 150)
    ///     .append_bytes(2, vec![0xF0, 0x00])
    ///     .append_repeated_string(3, &["valid utf8 string", "hello"])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_string(3).unwrap(), ["valid utf8 string".to_string(), "hello".to_string()]);
    /// ```
    pub fn repeated_string(&self, field_number: u32) -> Result<Vec<String>, RepeatedError> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::VariableLength(data) => out.push(
                    String::from_utf8(data.to_vec()).map_err(|_e| RepeatedError::InvalidUtf8)?,
                ),
                _ => return Err(RepeatedError::TypeMismatch),
            }
        }
        Ok(out)
    }

    /// Gets the value of the given field number. This returns None if
    /// the field number does not exist
    pub fn value(&self, field_number: u32) -> Option<Value> {
        self.value_ref(field_number).cloned()
    }

    /// Gets the last value of the given field number as a reference.
    /// This allows us to comply to the "Last One Wins" rule: <https://protobuf.dev/programming-guides/encoding/#last-one-wins>.
    /// This returns None if the field number does not exist.
    fn value_ref(&self, field_number: u32) -> Option<&Value<'_>> {
        match self.fields.get(&field_number) {
            Some(field) => field.last(),
            None => None,
        }
    }

    fn repeated_value_ref(&self, field_number: u32) -> &Vec<Value<'_>> {
        self.fields.get(&field_number).unwrap_or(&self.empty_vec)
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
            .append_repeated_uint64(7, &[150, 42, 1, 0, 0xFFFFFFFFFFFFFFFF])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.fields.len(), 1);
        assert_eq!(
            decoded.fields.get(&7).unwrap(),
            &[
                Value::Varint(150),
                Value::Varint(42),
                Value::Varint(1),
                Value::Varint(0),
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
    fn bytes_works() {
        let serialized = Anybuf::new()
            .append_uint64(1, 150)
            .append_bytes(2, vec![0xF0, 0x00])
            .append_bytes(3, vec![])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.bytes(1), None); // wrong type
        assert_eq!(decoded.bytes(2), Some(vec![0xF0, 0x00]));
        assert_eq!(decoded.bytes(3), Some(vec![]));
        assert_eq!(decoded.bytes(4), Some(vec![]));
    }

    #[test]
    fn string_works() {
        let serialized = Anybuf::new()
            .append_uint64(1, 150)
            .append_string(2, "blub")
            .append_string(3, "")
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.string(1), None);
        assert_eq!(decoded.string(2), Some("blub".to_string()));
        assert_eq!(decoded.string(3), Some("".to_string()));
        assert_eq!(decoded.string(4), Some("".to_string()));

        // Last One Wins (https://protobuf.dev/programming-guides/encoding/#last-one-wins)
        let serialized = Anybuf::new()
            .append_uint64(1, 150)
            .append_string(2, "one")
            .append_string(2, "two")
            .append_string(2, "three")
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.string(1), None);
        assert_eq!(decoded.string(2), Some("three".to_string()));
    }

    #[test]
    fn repeated_string_works() {
        // two strings
        let serialized = Anybuf::new()
            .append_repeated_string(7, &["foo", "bar"])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_string(7).unwrap(), &["foo", "bar"]);

        // duplicates and empty values
        let serialized = Anybuf::new()
            .append_repeated_string(7, &["foo", "foo", "", "ok"])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(
            decoded.repeated_string(7).unwrap(),
            &["foo", "foo", "", "ok"]
        );

        // empty list
        let serialized = Anybuf::new().append_repeated_string(7, &[]).into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_string(7).unwrap(), Vec::<String>::new());
    }

    #[test]
    fn uint64_works() {
        let serialized = Anybuf::new()
            .append_uint64(1, 150)
            .append_uint64(2, 17)
            .append_uint64(3, 36028797018963970)
            .append_bytes(4, vec![0xF0, 0x00])
            .append_uint64(5, 0)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.uint64(1), Some(150));
        assert_eq!(decoded.uint64(2), Some(17));
        assert_eq!(decoded.uint64(3), Some(36028797018963970));
        assert_eq!(decoded.uint64(4), None); // wrong type
        assert_eq!(decoded.uint64(5), Some(0));
        assert_eq!(decoded.uint64(6), Some(0));
    }

    #[test]
    fn uint32_works() {
        let serialized = Anybuf::new()
            .append_uint32(1, 150)
            .append_uint64(2, 17)
            .append_uint64(3, 36028797018963970)
            .append_bytes(4, vec![0xF0, 0x00])
            .append_uint32(5, 0)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.uint32(1), Some(150));
        assert_eq!(decoded.uint32(2), Some(17)); // works because on the wire we don't differentiate
        assert_eq!(decoded.uint32(3), None); // too large
        assert_eq!(decoded.uint32(4), None);
        assert_eq!(decoded.uint32(5), Some(0));
        assert_eq!(decoded.uint32(6), Some(0));
    }

    #[test]
    fn bool_works() {
        let serialized = Anybuf::new()
            .append_uint32(1, 150)
            .append_uint64(2, 17)
            .append_uint64(3, 1)
            .append_bytes(4, vec![0xF0, 0x00])
            .append_bool(5, true)
            .append_bool(6, false)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.bool(1), None); // too large
        assert_eq!(decoded.bool(2), None); // too large
        assert_eq!(decoded.bool(3), Some(true)); // 1 and true cannot be differentiated
        assert_eq!(decoded.bool(4), None); // wrong type
        assert_eq!(decoded.bool(5), Some(true));
        assert_eq!(decoded.bool(6), Some(false));
        assert_eq!(decoded.bool(7), Some(false));
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
