//! A minimal (like seriously), zero dependency protobuf encoder.
//!
//! Supported:
//! - Varint (u64)
//! - Repeated: Just append a field multiple times
//! - Nested: Just append an `Anybuf` instance
//!
//! Non supported:
//!
//! - Fixed length types
//! - Field sorting

use varint::{to_zigzag32, to_zigzag64};

mod varint;

#[derive(Default)]
pub struct Anybuf {
    output: Vec<u8>,
}

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

/// Encodes the unsigned integer `n` using the protobuf varint (variable integer)
/// format.
fn unsigned_varint_encode(mut n: u64, dest: &mut Vec<u8>) {
    let mut buf = [0u8; 10];
    let mut len = 0;
    loop {
        // Read least significant 7 bits
        let mut b = (n & 0b0111_1111) as u8;
        n >>= 7;
        // Set top bit when not yet done
        if n != 0 {
            b |= 0b1000_0000;
        }
        buf[len] = b;
        len += 1;
        if n == 0 {
            break;
        }
    }
    dest.extend_from_slice(&buf[0..len]);
}

impl Anybuf {
    /// Creates a new serializer.
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
    #[inline]
    pub fn append_string(self, field_number: u32, data: impl AsRef<str>) -> Self {
        self.append_bytes(field_number, data.as_ref().as_bytes())
    }

    /// Appends a uint64 field with the given field number.
    pub fn append_uint64(mut self, field_number: u32, value: u64) -> Self {
        if value == 0 {
            return self;
        }
        self.append_tag(field_number, WireType::Varint);
        unsigned_varint_encode(value, &mut self.output);
        self
    }

    /// Appends a uint32 field with the given field number.
    #[inline]
    pub fn append_uint32(self, field_number: u32, value: u32) -> Self {
        self.append_uint64(field_number, value.into())
    }

    /// Appends a bool field with the given field number.
    #[inline]
    pub fn append_bool(self, field_number: u32, value: bool) -> Self {
        self.append_uint64(field_number, value.into())
    }

    /// Appends an sint32 field with the given field number.
    ///
    /// Please note that protobuf has two different 32 bit signed integer types
    /// with different encodings: sint32 and int32. This only works for the former.
    pub fn append_sint32(self, field_number: u32, value: i32) -> Self {
        self.append_uint32(field_number, to_zigzag32(value))
    }

    /// Appends an sint64 field with the given field number.
    ///
    /// Please note that protobuf has two different 64 bit signed integer types
    /// with different encodings: sint64 and int64. This only works for the former.
    pub fn append_sint64(self, field_number: u32, value: i64) -> Self {
        self.append_uint64(field_number, to_zigzag64(value))
    }

    /// Appends a nested protobuf message with the given field number.
    pub fn append_message(self, field_number: u32, value: &Anybuf) -> Self {
        self.append_bytes(field_number, value.as_bytes())
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.output
    }

    /// Takes the instance and returns the protobuf bytes
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
    fn unsigned_varint_encode_works() {
        // examples from https://github.com/multiformats/unsigned-varint
        for (value, expected) in [
            (1, vec![0x01]),
            (127, vec![0x7f]),
            (128, vec![0x80, 0x01]),
            (255, vec![0xff, 0x01]),
            (300, vec![0xac, 0x02]),
            (16384, vec![0x80, 0x80, 0x01]),
        ] {
            let mut dest = Vec::new();
            unsigned_varint_encode(value, &mut dest);
            assert_eq!(dest, expected);
        }

        // https://ngtzeyang94.medium.com/go-with-examples-protobuf-encoding-mechanics-54ceff48ebaa
        let mut dest = Vec::new();
        unsigned_varint_encode(18789, &mut dest);
        assert_eq!(dest, [229, 146, 1]);

        // From https://github.com/tokio-rs/prost/blob/v0.12.1/src/encoding.rs#L1626-L1678
        let tests: Vec<(u64, &[u8])> = vec![
            (2u64.pow(0) - 1, &[0x00]),
            (2u64.pow(0), &[0x01]),
            (2u64.pow(7) - 1, &[0x7F]),
            (2u64.pow(7), &[0x80, 0x01]),
            (300, &[0xAC, 0x02]),
            (2u64.pow(14) - 1, &[0xFF, 0x7F]),
            (2u64.pow(14), &[0x80, 0x80, 0x01]),
            (2u64.pow(21) - 1, &[0xFF, 0xFF, 0x7F]),
            (2u64.pow(21), &[0x80, 0x80, 0x80, 0x01]),
            (2u64.pow(28) - 1, &[0xFF, 0xFF, 0xFF, 0x7F]),
            (2u64.pow(28), &[0x80, 0x80, 0x80, 0x80, 0x01]),
            (2u64.pow(35) - 1, &[0xFF, 0xFF, 0xFF, 0xFF, 0x7F]),
            (2u64.pow(35), &[0x80, 0x80, 0x80, 0x80, 0x80, 0x01]),
            (2u64.pow(42) - 1, &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]),
            (2u64.pow(42), &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01]),
            (
                2u64.pow(49) - 1,
                &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F],
            ),
            (
                2u64.pow(49),
                &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01],
            ),
            (
                2u64.pow(56) - 1,
                &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F],
            ),
            (
                2u64.pow(56),
                &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01],
            ),
            (
                2u64.pow(63) - 1,
                &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F],
            ),
            (
                2u64.pow(63),
                &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01],
            ),
            (
                u64::MAX,
                &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x01],
            ),
        ];
        for (value, expected) in tests {
            let mut dest = Vec::new();
            unsigned_varint_encode(value, &mut dest);
            assert_eq!(dest, expected);
        }

        // https://codeberg.org/ft/ufw/src/tag/v4.1.0/test/t-varint.c#L90-L101 and
        // https://codeberg.org/ft/ufw/src/tag/v4.1.0/test/t-varint.c#L39-L52
        for (value, expected) in [
            (0, vec![0x00]),
            (128, vec![0x80, 0x01]),
            (1234, vec![0xd2, 0x09]),
            (u32::MAX as u64, vec![0xff, 0xff, 0xff, 0xff, 0x0f]),
            (
                u64::MAX,
                vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01],
            ),
        ] {
            let mut dest = Vec::new();
            unsigned_varint_encode(value, &mut dest);
            assert_eq!(dest, expected);
        }
    }
}
