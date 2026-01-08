# AlgoC

A transpiler that takes algorithms written in a custom pseudocode DSL and outputs optimized, memory-safe implementations in multiple target languages.

## Overview

AlgoC is designed for implementing cryptographic algorithms, compression, codecs, and other performance-critical code that needs to work across multiple languages while maintaining correctness and safety.

## Features

- **Custom DSL** - Rust/C-like syntax with explicit memory annotations
- **Type Safety** - Strong type system with integer widening, references, arrays, and slices
- **Multiple Targets** - Generate code for JavaScript and Python
- **Endian Types** - First-class endianness support with `u32be`, `u32le`, etc.
- **Built-in Functions** - `rotr`, `rotl`, `bswap`, `read_u32_be`, `write_u64_be`, etc.
- **Import System** - Modular code organization with `use` statements
- **Test Framework** - Embedded test vectors for verification
- **Standard Library** - Cryptographic (SHA-256, MD5) and compression (DEFLATE, gzip) implementations

## Installation

```bash
cargo build --release
```

## Usage

```bash
# Type-check a file
algoc check stdlib/crypto/sha256.algoc

# Compile to JavaScript
algoc compile stdlib/crypto/sha256.algoc -t js

# Compile to Python
algoc compile stdlib/crypto/sha256.algoc -t py

# Compile with custom output path
algoc compile stdlib/crypto/sha256.algoc -t js -o output.js

# Include test functions in output
algoc compile stdlib/crypto/sha256.algoc -t js --test
```

## Example

```algoc
use "stdlib/runtime.algoc"

// SHA-256 round constants
const K: u32[64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    // ...
];

struct Sha256State {
    h: u32[8],
    block: u8[64],
    block_len: u8,
    total_len: u64
}

fn sha256_compress(state: &mut Sha256State, block: &[u8; 64]) {
    let mut w: u32[64];

    // Read big-endian values using endian casting
    for i in 0..16 {
        w[i] = block[i * 4..i * 4 + 4] as u32be;
    }

    for i in 16..64 {
        let s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
        let s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    // ...
}

// Write back using endian cast assignment
fn write_hash(output: &mut [u8], h: &[u32; 8]) {
    for i in 0..8 {
        output[i * 4..i * 4 + 4] as u32be = h[i];
    }
}

// Test vectors
test sha256_abc {
    input: bytes("abc"),
    expect: hex("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
}
```

## Supported Targets

| Target | Status | Notes |
|--------|--------|-------|
| JavaScript | ✅ Working | Uses TypedArrays for byte buffers |
| Python | ✅ Working | Uses bytearray for mutable buffers |
| Go | 🚧 Planned | |
| Rust | 🚧 Planned | |
| C | 🚧 Planned | |

## DSL Reference

### Types

- **Integers**: `u8`, `u16`, `u32`, `u64`, `u128`, `i8`, `i16`, `i32`, `i64`, `i128`
- **Endian Integers**: `u16be`, `u16le`, `u32be`, `u32le`, `u64be`, `u64le` (and signed variants)
- **Boolean**: `bool`
- **Arrays**: `T[N]` (e.g., `u32[64]`)
- **Array Repeat**: `[value; N]` (e.g., `[0u8; 64]` creates 64 zero bytes)
- **Slices**: `&[T]` (dynamically-sized view)
- **References**: `&T`, `&mut T`
- **Structs**: Named aggregate types

### Endian Casting

Endian-qualified types enable concise byte-order conversions:

```algoc
// Read a big-endian u32 from a byte slice
let value = buf[0..4] as u32be;

// Write a big-endian u32 to a byte slice
buf[0..4] as u32be = value;

// Works with any endian type
let le_value = data[offset..offset + 8] as u64le;
```

### Built-in Functions

| Function | Description |
|----------|-------------|
| `rotr(x, n)` | Rotate right |
| `rotl(x, n)` | Rotate left |
| `bswap(x)` | Byte swap |
| `read_u32_be(buf, offset)` | Read 32-bit big-endian |
| `read_u32_le(buf, offset)` | Read 32-bit little-endian |
| `write_u32_be(buf, offset, value)` | Write 32-bit big-endian |
| `write_u64_be(buf, offset, value)` | Write 64-bit big-endian |
| `secure_zero(buf)` | Securely zero memory |
| `constant_time_eq(a, b)` | Constant-time comparison |
| `assert(condition)` | Runtime assertion (for tests) |
| `len(slice)` | Get slice length |

### Imports

```algoc
// Import functions and types from another file
use "stdlib/runtime.algoc"
use "stdlib/hash/crc32.algoc"
```

### Control Flow

```algoc
// For loops with ranges
for i in 0..64 { }
for i in 0..=63 { }  // inclusive

// While loops
while condition { }

// Infinite loops
loop {
    if done { break; }
    continue;
}

// Conditionals
if condition {
} else if other {
} else {
}
```

## Standard Library

The `stdlib/` directory contains reference implementations:

### Cryptographic
- **SHA-256** (`stdlib/crypto/sha256.algoc`) - FIPS 180-4 compliant
- **MD5** (`stdlib/crypto/md5.algoc`) - RFC 1321 implementation

### Compression
- **DEFLATE** (`stdlib/compression/deflate.algoc`) - RFC 1951 decompression with Huffman decoding
- **Gzip** (`stdlib/compression/gzip.algoc`) - RFC 1952 container format

### Hash
- **CRC32** (`stdlib/hash/crc32.algoc`) - Checksum computation

### Runtime
- **runtime.algoc** (`stdlib/runtime.algoc`) - Bit manipulation utilities, endian helpers

## Architecture

```
Source (.algoc)
     │
     ▼
┌─────────┐
│  Lexer  │  Tokenization
└────┬────┘
     │
     ▼
┌─────────┐
│ Parser  │  AST construction
└────┬────┘
     │
     ▼
┌──────────┐
│ Resolver │  Name resolution, symbol tables
└────┬─────┘
     │
     ▼
┌─────────┐
│ Checker │  Type checking
└────┬────┘
     │
     ▼
┌───────────┐
│ Validator │  Semantic validation
└────┬──────┘
     │
     ▼
┌─────────┐
│ CodeGen │  Target-specific generation
└────┬────┘
     │
     ▼
Output (.js, .py, .go, .rs, .c)
```

## License

MIT
