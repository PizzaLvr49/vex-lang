# Vixen Bytecode Project

## Overview

Vixen is a portable bytecode runtime environment that combines the convenience of the JVM with the performance of native code.

The project is heavily inspired by other VMs such as [Luau](https://luau.org) and the [JVM](https://en.wikipedia.org/wiki/Java_virtual_machine).

## Goals

### Performance

Vixen is designed for predictable, high-performance execution:

- **Manual memory management** eliminates garbage collection pauses
- **Direct byte matching** on opcodes enables jump table optimization for fast dispatch
- **64-bit registers** with native SIMD support (f32x4, f64x2) for parallel operations
- **Fixed struct offsets** provide zero-overhead data structure access

### Portability

Write once, run anywhere:

- **`.vxpack` files** contain portable bytecode that runs on any platform
- **Static imports** are resolved when loading modules for self-contained execution
- **Stable bytecode format** ensures long-term compatibility
- **Uniform calling conventions** enable cross-platform development

### Capabilities

Modern runtime features without sacrificing performance:

- **Reflection**: Runtime introspection for serialization and debugging
- **Dynamic Loading**: Load and execute modules at runtime
- **Hot Reload**: Modify code during development without restarting
- **Sandboxing**: Safe execution of untrusted code with memory and permission restrictions
- **FFI**: Call native code when needed for platform-specific functionality

## Architecture

### Bytecode Format

Vixen uses a compact 32-bit instruction format:

```text
[opcode: 8 bits][dest: 8 bits][src1: 8 bits][src2: 8 bits]
```

Instructions operate on:

- 256 general-purpose 64-bit registers (r0-r255)
- 256 SIMD 128-bit registers (v0-v255)

Some instructions use multi-word encoding for immediate values:

```vxn
LOAD_IMM r5        ; First word: opcode + register
0x12345678         ; Second word: immediate value
```

### Memory Model

- **Handles**: Generational indices prevent use-after-free errors without garbage collection
- **Explicit Control**: Manual allocation and deallocation for predictable performance
- **Value Types**: Structs have predictable memory layout with no boxing overhead

### Type System

- **Structs**: Data structures with predefined field offsets
- **No Classes**: No inheritance or object-oriented constructs
- **Static Typing**: Types are known to the VM for optimal performance

## Standard Library

- **vixen.io**: File and network I/O operations
- **vixen.sys**: System calls and process management
- **vixen.math**: SIMD math utilities and vector operations
- **vixen.ffi**: Foreign function interface for calling native code

## Package Format

`.vxpack` files contain:

- **CODE**: Bytecode instructions
- **DATA**: Constant pool (numbers, strings)
- **TYPES**: Struct definitions and metadata
- **EXPORTS**: Public function definitions
- **IMPORTS**: External dependencies

## Getting Started

```bash
# Run a Vixen application
vixen run myapp.vxpack
```

## Status

Vixen is currently in active development. Core components being implemented:

- Interpreter with optimized dispatch
- Standard library design
