# Anybuf

Anybuf is a minimal (like seriously), zero dependency protobuf encoder
to encode anything.
It is designed to create the `value` bytes of a protobuf `Any`, hence the name.

Anybuf allows you to do things wrong in many ways and you should have a
solid understanding of how protobuf encoding works in general to better
understand the API.

## Non goals

- ~~Decoding~~ (Upcoming in <https://github.com/noislabs/anybuf/pull/2>)
- protobuf 2 things
- Field sorting
- Groups support (deprecated, see <https://protobuf.dev/programming-guides/proto2/#groups>)

## Supported:

- Varint fields (bool/uint32/uint64/sint32/sint64)
- Variable length fields (string/bytes)
- Repeated (bool/uint32/uint64/string/bytes/messages)
- Nested: Just append an `Anybuf` instance

## Not yet supported

- Fixed length types
- Packed encoding for repeated fields
- int32/int64

## How to use it

```rust
use anybuf::Anybuf;

let data = Anybuf::new()
    .append_uint64(1, 4)        // field number 1 gets value 4
    .append_string(2, "hello")  // field number 2 gets a string
    .append_bytes(3, b"hello")  // field number 3 gets bytes
    .append_message(4, &Anybuf::new().append_bool(3, true)) // field 4 gets a message
    .append_repeated_uint64(5, &[23, 56, 192])              // field number 5 is a repeated uint64
    .into_vec();                // done

// data is now a serialized protobuf doocument
```
