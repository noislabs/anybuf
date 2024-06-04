//! A minimal, zero dependency protobuf encoder and decoder to encode/decode anything.
//! It is designed to create the `value` bytes of a protobuf `Any`, hence the name.
//!
//! Due to its low level design, anybuf allows you to do things wrong in many ways
//! and you should have a solid understanding of how protobuf encoding works in
//! general to better understand the API.
//!
//! The crate anybuf is split in two major components:
//!
//! - [`anybuf::Anybuf`][crate::Anybuf] is a protobuf encoder
//! - [`anybuf::Bufany`][crate::Bufany] is a protobuf decoder
//!
//! ## Non goals
//! - protobuf 2 things
//! - Field sorting
//! - Groups support (deprecated, see <https://protobuf.dev/programming-guides/proto2/#groups>)
//!
//! ## Supported
//! - Varint fields (bool/uint32/uint64/sint32/sint64/int32/int64)
//! - Variable length fields (string/bytes)
//! - Nested messages: Just append an `Anybuf` instance
//! - Repeated (bool/uint32/uint64/sint32/sint64/int32/int64/string/bytes/messages)
//!
//! ## Not yet supported
//! - Fixed length types
//! - Packed encoding for repeated fields
//! - Maps support (but you can use the equivalent [encoding via repeated messages](https://protobuf.dev/programming-guides/encoding/#maps))

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod anybuf;
mod bufany;
mod slice_reader;
mod varint;

pub use crate::anybuf::Anybuf;
pub use crate::bufany::{Bufany, BufanyError};
