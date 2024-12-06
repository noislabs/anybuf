use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use crate::{
    slice_reader::SliceReader,
    varint::{from_zigzag32, from_zigzag64, read_unsigned_varint},
};

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
    fields: BTreeMap<u32, Vec<Value<'a>>>,
    // A vector that is always empty and has the lifetime we need.
    empty_vec: Vec<Value<'a>>,
}

#[derive(Debug, PartialEq)]
pub enum BufanyError {
    /// Found tag that is either not valid protobuf or unsuppored
    InvalidTag,
    /// Field number must be between 1 and 536,870,911
    InvalidFieldNumber,
    UnsupportedWireType(u8),
    ErrorDecodingVarint,
    /// The remaining data is not long enough to read the expected length
    UnexpectedEndOfData,
}

#[derive(Debug, PartialEq)]
pub enum RepeatedStringError {
    /// Found a value of the wrong wire type
    TypeMismatch,
    /// A variable length field did not contain valid UTF-8.
    InvalidUtf8,
}

#[derive(Debug, PartialEq)]
pub enum RepeatedMessageError {
    /// Found a value of the wrong wire type
    TypeMismatch,
    /// Found a value that cannot be decoded
    DecodingError(BufanyError),
}

impl core::fmt::Display for BufanyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Error decoding protobuf: ")?;
        match self {
            BufanyError::InvalidTag => f.write_str("Invalid tag"),
            BufanyError::InvalidFieldNumber => {
                f.write_str("Invalid field number, must be between 1 and 536,870,911")
            }
            BufanyError::UnsupportedWireType(wire_type) => {
                write!(f, "Unsupported wire type: {}", wire_type)
            }
            BufanyError::ErrorDecodingVarint => f.write_str("Error decoding varint"),
            BufanyError::UnexpectedEndOfData => f.write_str("Unexpected end of data"),
        }
    }
}

impl core::fmt::Display for RepeatedStringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Error decoding repeated string: ")?;
        match self {
            RepeatedStringError::TypeMismatch => {
                f.write_str("Found a value of the wrong wire type")
            }
            RepeatedStringError::InvalidUtf8 => {
                f.write_str("A variable length field did not contain valid UTF-8")
            }
        }
    }
}

impl core::fmt::Display for RepeatedMessageError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Error decoding repeated message: ")?;
        match self {
            RepeatedMessageError::TypeMismatch => {
                f.write_str("Found a value of the wrong wire type")
            }
            RepeatedMessageError::DecodingError(_) => {
                f.write_str("Could not decode nested message")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for BufanyError {}

#[cfg(feature = "std")]
impl std::error::Error for RepeatedStringError {}

#[cfg(feature = "std")]
impl std::error::Error for RepeatedMessageError {}

impl Bufany<'_> {
    /// Creates an empty instance with the given lifetime.
    ///
    /// This is a private constructor. Users of the library should always use [`Bufany::deserialize`].
    fn new<'a>() -> Bufany<'a> {
        Bufany {
            fields: Default::default(),
            empty_vec: Default::default(),
        }
    }
}

impl<'a> Bufany<'a> {
    /// Creates a new serializer.
    pub fn deserialize(serialized: &'a [u8]) -> Result<Bufany<'a>, BufanyError> {
        let mut out = Bufany::new::<'a>();

        let mut reader = SliceReader::new(serialized);

        loop {
            if reader.is_empty() {
                break;
            }

            let Some(tag) = read_unsigned_varint(&mut reader) else {
                return Err(BufanyError::InvalidTag);
            };

            // valid field numbers are between 1 and 536,870,911
            let field_number = match tag >> 3 {
                1..=536870911 => (tag >> 3) as u32,
                _ => return Err(BufanyError::InvalidFieldNumber),
            };
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
    /// - the value is not 0 or 1
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

    /// Gets a sint64 from the given field number.
    /// This returns None if the value type is not of type varint.
    ///
    /// Please note that protobuf has two different 64 bit signed integer types
    /// with different encodings: sint64 and int64. This only works for sint64.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_sint64(1, 150)
    ///     .append_sint64(2, -534214672)
    ///     .append_sint64(3, 0)
    ///     .append_bytes(4, vec![0xF0, 0x00])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.sint64(1), Some(150));
    /// assert_eq!(decoded.sint64(2), Some(-534214672));
    /// assert_eq!(decoded.sint64(3), Some(0));
    /// assert_eq!(decoded.sint64(4), None);
    /// assert_eq!(decoded.sint64(5), Some(0));
    /// ```
    pub fn sint64(&self, field_number: u32) -> Option<i64> {
        match self.value_ref(field_number) {
            Some(Value::Varint(data)) => Some(from_zigzag64(*data)),
            Some(_) => None, // found but wrong type
            None => Some(0), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets a sint32 from the given field number.
    /// This returns None if the value type is not of type varint
    /// or the value exceeds the 32 bit range.
    ///
    /// Please note that protobuf has two different 32 bit signed integer types
    /// with different encodings: sint32 and int32. This only works for sint32.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_sint32(1, 150)
    ///     .append_sint32(2, -534214672)
    ///     .append_sint32(3, 0)
    ///     .append_bytes(4, vec![0xF0, 0x00])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.sint32(1), Some(150));
    /// assert_eq!(decoded.sint32(2), Some(-534214672));
    /// assert_eq!(decoded.sint32(3), Some(0));
    /// assert_eq!(decoded.sint32(4), None);
    /// assert_eq!(decoded.sint32(5), Some(0));
    /// ```
    pub fn sint32(&self, field_number: u32) -> Option<i32> {
        match self.value_ref(field_number) {
            Some(Value::Varint(data)) => Some(from_zigzag32((*data).try_into().ok()?)),
            Some(_) => None, // found but wrong type
            None => Some(0), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets an int64 from the given field number.
    /// This returns None if the value type is not of type varint.
    ///
    /// Please note that protobuf has two different 64 bit signed integer types
    /// with different encodings: sint64 and int64. This only works for int64.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_int64(1, 150)
    ///     .append_int64(2, -534214672)
    ///     .append_int64(3, 0)
    ///     .append_bytes(4, vec![0xF0, 0x00])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.int64(1), Some(150));
    /// assert_eq!(decoded.int64(2), Some(-534214672));
    /// assert_eq!(decoded.int64(3), Some(0));
    /// assert_eq!(decoded.int64(4), None);
    /// assert_eq!(decoded.int64(5), Some(0));
    /// ```
    pub fn int64(&self, field_number: u32) -> Option<i64> {
        match self.value_ref(field_number) {
            Some(Value::Varint(data)) => Some(*data as i64),
            Some(_) => None, // found but wrong type
            None => Some(0), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets an int32 from the given field number.
    /// This returns None if the value type is not of type varint
    /// or the value exceeds the 32 bit range.
    ///
    /// Please note that protobuf has two different 32 bit signed integer types
    /// with different encodings: sint32 and int32. This only works for int32.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_int32(1, 150)
    ///     .append_int32(2, -534214672)
    ///     .append_int32(3, 0)
    ///     .append_bytes(4, vec![0xF0, 0x00])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.int32(1), Some(150));
    /// assert_eq!(decoded.int32(2), Some(-534214672));
    /// assert_eq!(decoded.int32(3), Some(0));
    /// assert_eq!(decoded.int32(4), None);
    /// assert_eq!(decoded.int32(5), Some(0));
    /// ```
    pub fn int32(&self, field_number: u32) -> Option<i32> {
        match self.value_ref(field_number) {
            Some(Value::Varint(value)) => Some((*value as i64).try_into().ok()?),
            Some(_) => None, // found but wrong type
            None => Some(0), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets a nested message from the given field number.
    /// This returns None if the value type is not of type variable length or the inner message cannot be decoded.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_message(
    ///         1,
    ///         &Anybuf::new()
    ///             .append_bool(1, true)
    ///             .append_string(2, "foo")
    ///             .append_sint64(3, -37648762834),
    ///     )
    ///     .append_sint32(2, 150)
    ///     .append_bytes(3, b"\0\0\0\0\0\0\0\0\0\0\0\0\0\0")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    ///
    /// let nested = decoded.message(1).unwrap();
    /// assert_eq!(nested.bool(1), Some(true));
    /// assert_eq!(nested.string(2), Some("foo".to_string()));
    /// assert_eq!(nested.sint64(3), Some(-37648762834));
    ///
    /// assert!(decoded.message(2).is_none()); // wrong type
    /// assert!(decoded.message(3).is_none()); // not a valid proto message
    /// ```
    pub fn message(&'a self, field_number: u32) -> Option<Bufany<'a>> {
        match self.value_ref(field_number) {
            Some(Value::VariableLength(data)) => Some(Bufany::deserialize(data).ok()?),
            Some(_) => None,                   // found but wrong type
            None => Some(Bufany::new::<'a>()), // Field not serialized, i.e. can be the default value
        }
    }

    /// Gets repeated uint64 from the given field number.
    /// Returns None in case a wrong wire type was found.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_repeated_uint64(1, &[150])
    ///     .append_repeated_uint64(2, &[150, 0, u64::MAX])
    ///     .append_string(3, "foo")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_uint64(1), Some(vec![150]));
    /// assert_eq!(decoded.repeated_uint64(2), Some(vec![150, 0, u64::MAX]));
    /// assert_eq!(decoded.repeated_uint64(3), None);
    /// ```
    pub fn repeated_uint64(&self, field_number: u32) -> Option<Vec<u64>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::Varint(data) => out.push(*data),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated uint32 from the given field number.
    /// Returns None in case a wrong wire type was found or the value exceeds the 32 bit range.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_repeated_uint32(1, &[150])
    ///     .append_repeated_uint32(2, &[150, 0, u32::MAX])
    ///     .append_string(3, "foo")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_uint32(1), Some(vec![150]));
    /// assert_eq!(decoded.repeated_uint32(2), Some(vec![150, 0, u32::MAX]));
    /// assert_eq!(decoded.repeated_uint32(3), None);
    /// ```
    pub fn repeated_uint32(&self, field_number: u32) -> Option<Vec<u32>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::Varint(data) => out.push((*data).try_into().ok()?),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated bool from the given field number.
    /// Returns None in case a wrong wire type was found or the value is not 0 or 1.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_repeated_bool(1, &[true])
    ///     .append_repeated_bool(2, &[true, false, true])
    ///     .append_string(3, "foo")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_bool(1), Some(vec![true]));
    /// assert_eq!(decoded.repeated_bool(2), Some(vec![true, false, true]));
    /// assert_eq!(decoded.repeated_bool(3), None);
    /// ```
    pub fn repeated_bool(&self, field_number: u32) -> Option<Vec<bool>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::Varint(0) => out.push(false),
                Value::Varint(1) => out.push(true),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated sint64 from the given field number.
    /// Returns None in case a wrong wire type was found.
    ///
    /// Please note that protobuf has two different 64 bit signed integer types
    /// with different encodings: sint64 and int64. This only works for sint64.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_repeated_sint64(1, &[150, -150])
    ///     .append_repeated_sint64(2, &[150, 0, i64::MAX])
    ///     .append_string(3, "foo")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_sint64(1), Some(vec![150, -150]));
    /// assert_eq!(decoded.repeated_sint64(2), Some(vec![150, 0, i64::MAX]));
    /// assert_eq!(decoded.repeated_sint64(3), None);
    /// ```
    pub fn repeated_sint64(&self, field_number: u32) -> Option<Vec<i64>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::Varint(data) => out.push(from_zigzag64(*data)),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated sint32 from the given field number.
    /// Returns None in case a wrong wire type was found or the value exceeds the 32 bit range.
    ///
    /// Please note that protobuf has two different 32 bit signed integer types
    /// with different encodings: sint32 and int32. This only works for sint32.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_repeated_sint32(1, &[150, -150])
    ///     .append_repeated_sint32(2, &[150, 0, i32::MIN])
    ///     .append_string(3, "foo")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_sint32(1), Some(vec![150, -150]));
    /// assert_eq!(decoded.repeated_sint32(2), Some(vec![150, 0, i32::MIN]));
    /// assert_eq!(decoded.repeated_sint32(3), None);
    /// ```
    pub fn repeated_sint32(&self, field_number: u32) -> Option<Vec<i32>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::Varint(data) => out.push(from_zigzag32((*data).try_into().ok()?)),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated int64 from the given field number.
    /// Returns None in case a wrong wire type was found.
    ///
    /// Please note that protobuf has two different 64 bit signed integer types
    /// with different encodings: sint64 and int64. This only works for int64.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_repeated_int64(1, &[150, -150])
    ///     .append_repeated_int64(2, &[150, 0, i64::MAX])
    ///     .append_string(3, "foo")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_int64(1), Some(vec![150, -150]));
    /// assert_eq!(decoded.repeated_int64(2), Some(vec![150, 0, i64::MAX]));
    /// assert_eq!(decoded.repeated_int64(3), None);
    /// ```
    pub fn repeated_int64(&self, field_number: u32) -> Option<Vec<i64>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::Varint(data) => out.push(*data as i64),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated sint32 from the given field number.
    /// Returns None in case a wrong wire type was found or the value exceeds the 32 bit range.
    ///
    /// Please note that protobuf has two different 32 bit signed integer types
    /// with different encodings: sint32 and int32. This only works for int32.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_repeated_int32(1, &[150, -150])
    ///     .append_repeated_int32(2, &[150, 0, i32::MIN])
    ///     .append_string(3, "foo")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_int32(1), Some(vec![150, -150]));
    /// assert_eq!(decoded.repeated_int32(2), Some(vec![150, 0, i32::MIN]));
    /// assert_eq!(decoded.repeated_int32(3), None);
    /// ```
    pub fn repeated_int32(&self, field_number: u32) -> Option<Vec<i32>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::Varint(data) => out.push((*data as i64).try_into().ok()?),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated bytes from the given field number.
    /// Returns None in case a wrong wire type was found.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany};
    ///
    /// let myvec = vec![0xF0u8, 0x00];
    /// let serialized = Anybuf::new()
    ///     .append_uint64(1, 150)
    ///     .append_repeated_bytes(2, &[&myvec])
    ///     .append_repeated_bytes::<&[u8]>(3, &[b"\x01\x02\x03", b"\x00"])
    ///     .append_repeated_string(4, &["valid utf8 string", "hello"])
    ///     .append_repeated_bytes::<&[u8]>(5, &[])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    /// assert_eq!(decoded.repeated_bytes(2).unwrap(), &[&[0xF0, 0x00]]);
    /// assert_eq!(decoded.repeated_bytes(3).unwrap(), [&[1u8, 2, 3] as &[u8], &[0]]);
    /// assert_eq!(decoded.repeated_bytes(4).unwrap(), [b"valid utf8 string" as &[u8], b"hello"]);
    /// assert_eq!(decoded.repeated_bytes(5).unwrap(), Vec::<Vec<u8>>::new());
    /// assert_eq!(decoded.repeated_bytes(12).unwrap(), Vec::<Vec<u8>>::new());
    /// ```
    pub fn repeated_bytes(&self, field_number: u32) -> Option<Vec<Vec<u8>>> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::VariableLength(data) => out.push(data.to_vec()),
                _ => return None, // Wrong type, we can't handle this
            }
        }
        Some(out)
    }

    /// Gets repeated string from the given field number.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany, RepeatedStringError};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_uint64(1, 150)
    ///     .append_bytes(2, vec![0xF0, 0x00])
    ///     .append_repeated_string(3, &["valid utf8 string", "hello"])
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    ///
    /// // happy path
    /// let strings = decoded.repeated_string(3).unwrap();
    /// assert_eq!(strings, ["valid utf8 string".to_string(), "hello".to_string()]);
    ///
    /// // cannot get strings from int field
    /// assert!(matches!(decoded.repeated_string(1).unwrap_err(), RepeatedStringError::TypeMismatch));
    /// ```
    pub fn repeated_string(&self, field_number: u32) -> Result<Vec<String>, RepeatedStringError> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Value::VariableLength(data) => out.push(
                    String::from_utf8(data.to_vec())
                        .map_err(|_e| RepeatedStringError::InvalidUtf8)?,
                ),
                _ => return Err(RepeatedStringError::TypeMismatch),
            }
        }
        Ok(out)
    }

    /// Gets repeated message from the given field number.
    ///
    /// Returns an error in case a wrong wire type was found
    /// or the message cannot be decoded.
    ///
    /// ## Example
    ///
    /// ```
    /// use anybuf::{Anybuf, Bufany, RepeatedMessageError};
    ///
    /// let serialized = Anybuf::new()
    ///     .append_message(
    ///         1,
    ///         &Anybuf::new()
    ///             .append_bool(1, true)
    ///             .append_string(2, "foo")
    ///             .append_sint64(3, -37648762834),
    ///     )
    ///     .append_message(
    ///         1,
    ///         &Anybuf::new()
    ///             .append_bool(1, true)
    ///             .append_string(2, "bar")
    ///             .append_sint64(3, -37648762834),
    ///     )
    ///     .append_message(
    ///         1,
    ///         &Anybuf::new()
    ///             .append_bool(1, true)
    ///             .append_string(2, "baz")
    ///             .append_sint64(3, -37648762834),
    ///     )
    ///     .append_sint32(2, 150)
    ///     .append_bytes(3, b"\0\0\0\0\0\0\0\0\0\0\0\0\0\0")
    ///     .into_vec();
    /// let decoded = Bufany::deserialize(&serialized).unwrap();
    ///
    /// let nested = decoded.repeated_message(1).unwrap();
    /// assert_eq!(nested.len(), 3);
    /// assert_eq!(nested[0].bool(1), Some(true));
    /// assert_eq!(nested[0].string(2), Some("foo".to_string()));
    /// assert_eq!(nested[0].sint64(3), Some(-37648762834));
    /// assert_eq!(nested[1].bool(1), Some(true));
    /// assert_eq!(nested[1].string(2), Some("bar".to_string()));
    /// assert_eq!(nested[1].sint64(3), Some(-37648762834));
    /// assert_eq!(nested[2].bool(1), Some(true));
    /// assert_eq!(nested[2].string(2), Some("baz".to_string()));
    /// assert_eq!(nested[2].sint64(3), Some(-37648762834));
    ///
    /// assert!(matches!(decoded.repeated_message(2).unwrap_err(), RepeatedMessageError::TypeMismatch)); // wrong type
    /// assert!(matches!(decoded.repeated_message(3).unwrap_err(), RepeatedMessageError::DecodingError(_))); // not a valid proto message
    /// ```
    pub fn repeated_message(
        &'a self,
        field_number: u32,
    ) -> Result<Vec<Bufany<'a>>, RepeatedMessageError> {
        let values = self.repeated_value_ref(field_number);
        let mut out = Vec::with_capacity(values.len());

        for value in values {
            let data = match value {
                Value::VariableLength(data) => *data,
                _ => return Err(RepeatedMessageError::TypeMismatch),
            };
            match Bufany::deserialize(data) {
                Ok(m) => out.push(m),
                Err(err) => return Err(RepeatedMessageError::DecodingError(err)),
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
    use alloc::string::ToString;
    use alloc::vec;

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
    fn sint64_works() {
        let serialized = Anybuf::new()
            .append_sint64(1, 150)
            .append_sint64(2, -534214672)
            .append_sint64(3, 0)
            .append_bytes(4, vec![0xF0, 0x00])
            .append_sint64(5, i64::MIN)
            .append_sint64(6, i64::MAX)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.sint64(1), Some(150));
        assert_eq!(decoded.sint64(2), Some(-534214672));
        assert_eq!(decoded.sint64(3), Some(0));
        assert_eq!(decoded.sint64(4), None);
        assert_eq!(decoded.sint64(5), Some(i64::MIN));
        assert_eq!(decoded.sint64(6), Some(i64::MAX));
        assert_eq!(decoded.sint64(85), Some(0)); // not serialized => default
    }

    #[test]
    fn sint32_works() {
        let serialized = Anybuf::new()
            .append_sint32(1, 150)
            .append_sint32(2, -534214672)
            .append_sint32(3, 0)
            .append_bytes(4, vec![0xF0, 0x00])
            .append_sint32(5, i32::MIN)
            .append_sint32(6, i32::MAX)
            .append_sint64(7, i32::MAX as i64 + 1)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.sint32(1), Some(150));
        assert_eq!(decoded.sint32(2), Some(-534214672));
        assert_eq!(decoded.sint32(3), Some(0));
        assert_eq!(decoded.sint32(4), None);
        assert_eq!(decoded.sint32(5), Some(i32::MIN));
        assert_eq!(decoded.sint32(6), Some(i32::MAX));
        assert_eq!(decoded.sint32(7), None); // value out of range
        assert_eq!(decoded.sint32(85), Some(0)); // not serialized => default
    }

    #[test]
    fn int64_works() {
        let serialized = Anybuf::new()
            .append_int64(1, 150)
            .append_int64(2, -534214672)
            .append_int64(3, 0)
            .append_bytes(4, vec![0xF0, 0x00])
            .append_int64(5, i64::MIN)
            .append_int64(6, i64::MAX)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.int64(1), Some(150));
        assert_eq!(decoded.int64(2), Some(-534214672));
        assert_eq!(decoded.int64(3), Some(0));
        assert_eq!(decoded.int64(4), None);
        assert_eq!(decoded.int64(5), Some(i64::MIN));
        assert_eq!(decoded.int64(6), Some(i64::MAX));
        assert_eq!(decoded.int64(85), Some(0)); // not serialized => default
    }

    #[test]
    fn int32_works() {
        let serialized = Anybuf::new()
            .append_int32(1, 150)
            .append_int32(2, -534214672)
            .append_int32(3, 0)
            .append_bytes(4, vec![0xF0, 0x00])
            .append_int32(5, i32::MIN)
            .append_int32(6, i32::MAX)
            .append_int64(7, i32::MAX as i64 + 1)
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.int32(1), Some(150));
        assert_eq!(decoded.int32(2), Some(-534214672));
        assert_eq!(decoded.int32(3), Some(0));
        assert_eq!(decoded.int32(4), None);
        assert_eq!(decoded.int32(5), Some(i32::MIN));
        assert_eq!(decoded.int32(6), Some(i32::MAX));
        assert_eq!(decoded.int32(7), None); // value out of range
        assert_eq!(decoded.int32(85), Some(0)); // not serialized => default
    }

    #[test]
    fn message_works() {
        let serialized = Anybuf::new()
            .append_message(
                1,
                &Anybuf::new()
                    .append_bool(1, true)
                    .append_string(2, "foo")
                    .append_sint64(3, -37648762834),
            )
            .append_sint32(2, 150)
            .append_bytes(3, b"\0\0\0\0\0\0\0\0\0\0\0\0\0\0")
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();

        let nested = decoded.message(1).unwrap();
        assert_eq!(nested.bool(1), Some(true));
        assert_eq!(nested.string(2), Some("foo".to_string()));
        assert_eq!(nested.sint64(3), Some(-37648762834));

        assert!(decoded.message(2).is_none()); // wrong type
        assert!(decoded.message(3).is_none()); // not a valid proto message
    }

    #[test]
    fn repeated_uint64_works() {
        let serialized = Anybuf::new()
            .append_repeated_uint64(1, &[150])
            .append_repeated_uint64(2, &[150, 0, u64::MAX])
            .append_string(3, "foo")
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_uint64(1), Some(vec![150]));
        assert_eq!(decoded.repeated_uint64(2), Some(vec![150, 0, u64::MAX]));
        assert_eq!(decoded.repeated_uint64(3), None);
        assert_eq!(decoded.repeated_uint64(85), Some(vec![])); // not serialized => default
    }

    #[test]
    fn repeated_uint32_works() {
        let serialized = Anybuf::new()
            .append_repeated_uint32(1, &[150])
            .append_repeated_uint32(2, &[150, 0, u32::MAX])
            .append_string(3, "foo")
            .append_repeated_uint64(4, &[150, 0, u64::MAX])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_uint32(1), Some(vec![150]));
        assert_eq!(decoded.repeated_uint32(2), Some(vec![150, 0, u32::MAX]));
        assert_eq!(decoded.repeated_uint32(3), None);
        assert_eq!(decoded.repeated_uint32(4), None); // Value exceeded 32 bit range
        assert_eq!(decoded.repeated_uint32(85), Some(vec![])); // not serialized => default
    }

    #[test]
    fn repeated_bool() {
        let serialized = Anybuf::new()
            .append_repeated_bool(1, &[true])
            .append_repeated_bool(2, &[true, false, true])
            .append_string(3, "foo")
            .append_repeated_uint64(4, &[0, 1, 17])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_bool(1), Some(vec![true]));
        assert_eq!(decoded.repeated_bool(2), Some(vec![true, false, true]));
        assert_eq!(decoded.repeated_bool(3), None);
        assert_eq!(decoded.repeated_bool(4), None); // Value exceeded 1 bit range
        assert_eq!(decoded.repeated_bool(85), Some(vec![])); // not serialized => default
    }

    #[test]
    fn repeated_sint64_works() {
        let serialized = Anybuf::new()
            .append_repeated_sint64(1, &[150, -150])
            .append_repeated_sint64(2, &[150, 0, i64::MIN, i64::MAX])
            .append_string(3, "foo")
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_sint64(1), Some(vec![150, -150]));
        assert_eq!(
            decoded.repeated_sint64(2),
            Some(vec![150, 0, i64::MIN, i64::MAX])
        );
        assert_eq!(decoded.repeated_sint64(3), None);
        assert_eq!(decoded.repeated_sint64(85), Some(vec![])); // not serialized => default
    }

    #[test]
    fn repeated_sint32_works() {
        let serialized = Anybuf::new()
            .append_repeated_sint32(1, &[150, -150])
            .append_repeated_sint32(2, &[150, 0, i32::MIN])
            .append_string(3, "foo")
            .append_repeated_sint64(4, &[150, 0, i64::MAX])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_sint32(1), Some(vec![150, -150]));
        assert_eq!(decoded.repeated_sint32(2), Some(vec![150, 0, i32::MIN]));
        assert_eq!(decoded.repeated_sint32(3), None);
        assert_eq!(decoded.repeated_sint32(4), None); // Value exceeded 32 bit range
        assert_eq!(decoded.repeated_sint32(85), Some(vec![])); // not serialized => default
    }

    #[test]
    fn repeated_int64_works() {
        let serialized = Anybuf::new()
            .append_repeated_int64(1, &[150, -150])
            .append_repeated_int64(2, &[150, 0, i64::MIN, i64::MAX])
            .append_string(3, "foo")
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_int64(1), Some(vec![150, -150]));
        assert_eq!(
            decoded.repeated_int64(2),
            Some(vec![150, 0, i64::MIN, i64::MAX])
        );
        assert_eq!(decoded.repeated_int64(3), None);
        assert_eq!(decoded.repeated_int64(85), Some(vec![])); // not serialized => default
    }

    #[test]
    fn repeated_int32_works() {
        let serialized = Anybuf::new()
            .append_repeated_int32(1, &[150, -150])
            .append_repeated_int32(2, &[150, 0, i32::MIN])
            .append_string(3, "foo")
            .append_repeated_int64(4, &[150, 0, i64::MAX])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        assert_eq!(decoded.repeated_int32(1), Some(vec![150, -150]));
        assert_eq!(decoded.repeated_int32(2), Some(vec![150, 0, i32::MIN]));
        assert_eq!(decoded.repeated_int32(3), None);
        assert_eq!(decoded.repeated_int32(4), None); // Value exceeded 32 bit range
        assert_eq!(decoded.repeated_int32(85), Some(vec![])); // not serialized => default
    }

    #[test]
    fn repeated_bytes_works() {
        let serialized = Anybuf::new()
            .append_uint64(1, 150)
            .append_repeated_bytes(2, &[vec![0xF0u8, 0x00].as_slice()])
            .append_repeated_bytes::<&[u8]>(3, &[b"\x01\x02\x03", b"\x00", b"", b"blub"])
            .append_repeated_string(4, &["valid utf8 string", "hello"])
            .append_repeated_bytes::<&[u8]>(5, &[])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        // Wrong type
        assert_eq!(decoded.repeated_bytes(1), None);
        // One element
        assert_eq!(decoded.repeated_bytes(2).unwrap(), [b"\xF0\0"]);
        // Multiple elements
        assert_eq!(
            decoded.repeated_bytes(3).unwrap(),
            [b"\x01\x02\x03" as &[u8], b"\x00", b"", b"blub"]
        );
        // String elements decoded as bytes
        assert_eq!(
            decoded.repeated_bytes(4).unwrap(),
            [b"valid utf8 string" as &[u8], b"hello"]
        );
        // No elements
        assert_eq!(decoded.repeated_bytes(5).unwrap(), Vec::<Vec<u8>>::new());
        // not serialized => default
        assert_eq!(decoded.repeated_bytes(85).unwrap(), Vec::<Vec<u8>>::new());
    }

    #[test]
    fn repeated_string_works() {
        let serialized = Anybuf::new()
            .append_repeated_sint32(1, &[1, 2, 3])
            .append_repeated_string(2, &["foo", "bar"])
            .append_repeated_string(3, &["foo", "foo", "", "ok"])
            .append_repeated_string::<String>(4, &[])
            .append_repeated_bytes(5, &[b"hello", b"world"])
            .append_repeated_bytes(6, &[b"\xf0\x00"])
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();
        // wrong type
        let err = decoded.repeated_string(1).unwrap_err();
        assert!(matches!(err, RepeatedStringError::TypeMismatch));
        // two strings
        assert_eq!(decoded.repeated_string(2).unwrap(), &["foo", "bar"]);
        // duplicates and empty values
        assert_eq!(
            decoded.repeated_string(3).unwrap(),
            &["foo", "foo", "", "ok"]
        );
        // empty list
        assert_eq!(decoded.repeated_string(4).unwrap(), Vec::<String>::new());
        // interprets repeated bytes as repeated string
        assert_eq!(decoded.repeated_string(5).unwrap(), &["hello", "world"]);
        // invalid-utf8 is rejected
        let err = decoded.repeated_string(6).unwrap_err();
        assert!(matches!(err, RepeatedStringError::InvalidUtf8));
        // not serialized => default
        assert_eq!(decoded.repeated_string(85).unwrap(), Vec::<String>::new());
    }

    #[test]
    fn repeated_message_works() {
        let serialized = Anybuf::new()
            .append_message(
                1,
                &Anybuf::new()
                    .append_bool(1, true)
                    .append_string(2, "foo")
                    .append_sint64(3, -37648762834),
            )
            .append_message(
                1,
                &Anybuf::new()
                    .append_bool(1, true)
                    .append_string(2, "bar")
                    .append_sint64(3, -37648762834),
            )
            .append_message(
                1,
                &Anybuf::new()
                    .append_bool(1, true)
                    .append_string(2, "baz")
                    .append_sint64(3, -37648762834),
            )
            .append_message(2, &Anybuf::new().append_uint32(1, 42))
            .append_message(3, &Anybuf::new())
            .append_sint32(10, 150)
            .append_message(
                11,
                &Anybuf::new()
                    .append_bool(1, true)
                    .append_string(2, "baz")
                    .append_sint64(3, -37648762834),
            )
            .append_uint32(11, 22)
            .append_bytes(12, b"\0\0\0\0\0\0\0\0\0\0\0\0\0\0")
            .into_vec();
        let decoded = Bufany::deserialize(&serialized).unwrap();

        let nested = decoded.repeated_message(1).unwrap();
        assert_eq!(nested.len(), 3);
        assert_eq!(nested[0].bool(1), Some(true));
        assert_eq!(nested[0].string(2), Some("foo".to_string()));
        assert_eq!(nested[0].sint64(3), Some(-37648762834));
        assert_eq!(nested[1].bool(1), Some(true));
        assert_eq!(nested[1].string(2), Some("bar".to_string()));
        assert_eq!(nested[1].sint64(3), Some(-37648762834));
        assert_eq!(nested[2].bool(1), Some(true));
        assert_eq!(nested[2].string(2), Some("baz".to_string()));
        assert_eq!(nested[2].sint64(3), Some(-37648762834));

        let nested = decoded.repeated_message(2).unwrap();
        assert_eq!(nested.len(), 1);
        assert_eq!(nested[0].uint32(1), Some(42));

        // An empty message is non existent
        let nested = decoded.repeated_message(3).unwrap();
        assert_eq!(nested.len(), 0);

        // int
        assert!(matches!(
            decoded.repeated_message(10).unwrap_err(),
            RepeatedMessageError::TypeMismatch
        ));
        // mixed type string and int
        assert!(matches!(
            decoded.repeated_message(11).unwrap_err(),
            RepeatedMessageError::TypeMismatch
        ));
        // invalid data in variable length field
        assert!(matches!(
            decoded.repeated_message(12).unwrap_err(),
            RepeatedMessageError::DecodingError(_)
        ));
    }
}
