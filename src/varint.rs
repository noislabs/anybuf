use crate::slice_reader::SliceReader;

#[allow(dead_code)]
#[inline]
pub fn to_zigzag32(n: i32) -> u32 {
    ((n << 1) ^ (n >> 31)) as u32
}

#[allow(dead_code)]
#[inline]
pub fn from_zigzag32(n: u32) -> i32 {
    ((n >> 1) as i32) ^ (-((n & 1) as i32))
}

#[allow(dead_code)]
#[inline]
pub fn to_zigzag64(n: i64) -> u64 {
    ((n << 1) ^ (n >> 63)) as u64
}

#[allow(dead_code)]
#[inline]
pub fn from_zigzag64(n: u64) -> i64 {
    ((n >> 1) as i64) ^ (-((n & 1) as i64))
}

/// Encodes the unsigned integer `n` using the protobuf varint (variable integer)
/// format.
pub fn unsigned_varint_encode(mut n: u64, dest: &mut Vec<u8>) {
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

/// Reads an unsigned varint from the given slice reader.
/// Returns `None` if the end of the slice is reached without completing the read or
/// if the varint exceeds a length of 10 bytes.
pub fn read_unsigned_varint(data: &mut SliceReader) -> Option<u64> {
    let mut out = 0u64;

    // If byte_counter becomes 10, the `value << (byte_counter * 7)` performs a
    // left shift of 70 bits on a u64 which leads to an overflow panic.
    for byte_counter in 0..10 {
        let Some(byte) = data.read_one() else {
            return None;
        };
        let value = (byte & 0x7f) as u64;
        out += value << (byte_counter * 7);
        if byte & 0x80 == 0 {
            return Some(out);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_zigzag32_works() {
        // values from https://protobuf.dev/programming-guides/encoding/
        assert_eq!(to_zigzag32(0), 0);
        assert_eq!(to_zigzag32(-1), 1);
        assert_eq!(to_zigzag32(1), 2);
        assert_eq!(to_zigzag32(-2), 3);
        assert_eq!(to_zigzag32(0x7fffffff), 0xfffffffe);
        assert_eq!(to_zigzag32(-0x80000000), 0xffffffff);

        // some more from https://lemire.me/blog/2022/11/25/making-all-your-integers-positive-with-zigzag-encoding/
        assert_eq!(to_zigzag32(15), 30);
        assert_eq!(to_zigzag32(-16), 31);
        assert_eq!(to_zigzag32(16), 32);
        assert_eq!(to_zigzag32(-17), 33);
        assert_eq!(to_zigzag32(17), 34);
        assert_eq!(to_zigzag32(-18), 35);
        assert_eq!(to_zigzag32(18), 36);
        assert_eq!(to_zigzag32(-19), 37);
        assert_eq!(to_zigzag32(19), 38);
        assert_eq!(to_zigzag32(-20), 39);
        assert_eq!(to_zigzag32(20), 40);
    }

    #[test]
    fn from_zigzag32_works() {
        // values from https://protobuf.dev/programming-guides/encoding/
        assert_eq!(from_zigzag32(0), 0);
        assert_eq!(from_zigzag32(1), -1);
        assert_eq!(from_zigzag32(2), 1);
        assert_eq!(from_zigzag32(3), -2);
        assert_eq!(from_zigzag32(0xfffffffe), 0x7fffffff);
        assert_eq!(from_zigzag32(0xffffffff), -0x80000000);

        // some more from https://lemire.me/blog/2022/11/25/making-all-your-integers-positive-with-zigzag-encoding/
        assert_eq!(from_zigzag32(30), 15);
        assert_eq!(from_zigzag32(31), -16);
        assert_eq!(from_zigzag32(32), 16);
        assert_eq!(from_zigzag32(33), -17);
        assert_eq!(from_zigzag32(34), 17);
        assert_eq!(from_zigzag32(35), -18);
        assert_eq!(from_zigzag32(36), 18);
        assert_eq!(from_zigzag32(37), -19);
        assert_eq!(from_zigzag32(38), 19);
        assert_eq!(from_zigzag32(39), -20);
        assert_eq!(from_zigzag32(40), 20);

        // Roundtrips work
        for i in 0..=30 {
            // Positive values form 0b00000000000000000000000000000001
            //                   to 0b01000000000000000000000000000000
            let n = 1 << i; // 2^i
            assert_eq!(from_zigzag32(to_zigzag32(n)), n);

            // Negative values form 0b10000000000000000000000000000001
            //                   to 0b01000000000000000000000000000000
            let n = (0b10000000000000000000000000000000u32 as i32) | (1 << i);
            assert_eq!(from_zigzag32(to_zigzag32(n)), n);
        }
    }

    #[test]
    fn to_zigzag64_works() {
        // values from https://protobuf.dev/programming-guides/encoding/
        assert_eq!(to_zigzag64(0), 0);
        assert_eq!(to_zigzag64(-1), 1);
        assert_eq!(to_zigzag64(1), 2);
        assert_eq!(to_zigzag64(-2), 3);
        assert_eq!(to_zigzag64(0x7fffffff), 0xfffffffe);
        assert_eq!(to_zigzag64(-0x80000000), 0xffffffff);

        assert_eq!(to_zigzag64(i64::MAX), u64::MAX - 1);
        assert_eq!(to_zigzag64(i64::MIN), u64::MAX);

        // some more from https://lemire.me/blog/2022/11/25/making-all-your-integers-positive-with-zigzag-encoding/
        assert_eq!(to_zigzag64(15), 30);
        assert_eq!(to_zigzag64(-16), 31);
        assert_eq!(to_zigzag64(16), 32);
        assert_eq!(to_zigzag64(-17), 33);
        assert_eq!(to_zigzag64(17), 34);
        assert_eq!(to_zigzag64(-18), 35);
        assert_eq!(to_zigzag64(18), 36);
        assert_eq!(to_zigzag64(-19), 37);
        assert_eq!(to_zigzag64(19), 38);
        assert_eq!(to_zigzag64(-20), 39);
        assert_eq!(to_zigzag64(20), 40);
    }

    #[test]
    fn from_zigzag64_works() {
        // values from https://protobuf.dev/programming-guides/encoding/
        assert_eq!(from_zigzag64(0), 0);
        assert_eq!(from_zigzag64(1), -1);
        assert_eq!(from_zigzag64(2), 1);
        assert_eq!(from_zigzag64(3), -2);
        assert_eq!(from_zigzag64(0xfffffffe), 0x7fffffff);
        assert_eq!(from_zigzag64(0xffffffff), -0x80000000);

        assert_eq!(from_zigzag64(u64::MAX - 1), i64::MAX);
        assert_eq!(from_zigzag64(u64::MAX), i64::MIN);

        // some more from https://lemire.me/blog/2022/11/25/making-all-your-integers-positive-with-zigzag-encoding/
        assert_eq!(from_zigzag64(30), 15);
        assert_eq!(from_zigzag64(31), -16);
        assert_eq!(from_zigzag64(32), 16);
        assert_eq!(from_zigzag64(33), -17);
        assert_eq!(from_zigzag64(34), 17);
        assert_eq!(from_zigzag64(35), -18);
        assert_eq!(from_zigzag64(36), 18);
        assert_eq!(from_zigzag64(37), -19);
        assert_eq!(from_zigzag64(38), 19);
        assert_eq!(from_zigzag64(39), -20);
        assert_eq!(from_zigzag64(40), 20);

        // Roundtrips work
        for i in 0..=62 {
            // Positive values form 0b0000000000000000000000000000000000000000000000000000000000000001
            //                   to 0b0100000000000000000000000000000000000000000000000000000000000000
            let n = 1 << i; // 2^i
            assert_eq!(from_zigzag64(to_zigzag64(n)), n);

            // Negative values form 0b1000000000000000000000000000000000000000000000000000000000000001
            //                   to 0b1100000000000000000000000000000000000000000000000000000000000000
            let n = (0b1000000000000000000000000000000000000000000000000000000000000000u64 as i64)
                | (1 << i);
            assert_eq!(from_zigzag64(to_zigzag64(n)), n);
        }
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

    #[test]
    fn read_unsigned_varint_handles_early_end() {
        // 3rd byte has a continuation bit but there is no more byte
        let a: &[u8] = &[0b10000111, 0b10000000, 0b10000000];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)), None);

        // empty
        let a: &[u8] = &[];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)), None);
    }

    #[test]
    fn read_unsigned_varint_is_length_limited() {
        // 1 bytes
        let a: &[u8] = &[0b00000111];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)).unwrap(), 7);
        // 2 bytes
        let a: &[u8] = &[0b10000111, 0b00000000];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)).unwrap(), 7);
        // 3 bytes
        let a: &[u8] = &[0b10000111, 0b10000000, 0b00000000];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)).unwrap(), 7);
        // 4 bytes
        let a: &[u8] = &[0b10000111, 0b10000000, 0b10000000, 0b00000000];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)).unwrap(), 7);
        // 10 bytes
        let a: &[u8] = &[
            0b10000111, 0b10000000, 0b10000000, 0b10000000, 0b10000000, 0b10000000, 0b10000000,
            0b10000000, 0b10000000, 0b00000000,
        ];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)).unwrap(), 7);
        // 11 bytes (too long)
        let a: &[u8] = &[
            0b10000111, 0b10000000, 0b10000000, 0b10000000, 0b10000000, 0b10000000, 0b10000000,
            0b10000000, 0b10000000, 0b10000000, 0b00000000,
        ];
        assert_eq!(read_unsigned_varint(&mut SliceReader::new(a)), None);
    }
}
