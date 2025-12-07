#![expect(incomplete_features, unused)]
#![feature(explicit_tail_calls)]

use anyhow::{Result, bail};
use std::{f64, io::Write};

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
enum Opcode {
    // Data - Primitives
    LoadConstI32 = 0x01,
    LoadConstI64 = 0x02,
    LoadConstF64 = 0x03,

    // Heap operations
    AllocString = 0x10, // Allocate string from pool
    AllocArray = 0x11,  // Allocate array with size
    Drop = 0x12,        // Free heap object

    // Array operations
    ArrayGet = 0x13, // Get element from array
    ArraySet = 0x14, // Set element in array
    ArrayLen = 0x15, // Get array length

    // String operations
    StringConcat = 0x16, // Concatenate two strings
    StringLen = 0x17,    // Get string length

    // General
    Move = 0x20,

    // Control
    SysCall = 0x30,
    Jump = 0x31,
    JumpZero = 0x32,

    // Arithmetic
    AddI32 = 0x40,
    SubI32 = 0x41,
    MulI32 = 0x42,

    Halt = 0xFF,
}

#[repr(C, align(4))]
#[derive(Debug, Clone, Copy)]
struct Instruction {
    opcode: u8,
    dest: u8,
    src1: u8,
    src2: u8,
}

macro_rules! instruction_builders {
    ($name:ident, $opcode:expr) => {
        #[inline(always)]
        fn $name() -> Self {
            Self {
                opcode: $opcode as u8,
                dest: 0,
                src1: 0,
                src2: 0,
            }
        }
    };

    ($name:ident, $opcode:expr, dest) => {
        #[inline(always)]
        fn $name(dest: u8) -> Self {
            Self {
                opcode: $opcode as u8,
                dest,
                src1: 0,
                src2: 0,
            }
        }
    };

    ($name:ident, $opcode:expr, dest, src1) => {
        #[inline(always)]
        fn $name(dest: u8, src1: u8) -> Self {
            Self {
                opcode: $opcode as u8,
                dest,
                src1,
                src2: 0,
            }
        }
    };

    ($name:ident, $opcode:expr, dest, src1, src2) => {
        #[inline(always)]
        fn $name(dest: u8, src1: u8, src2: u8) -> Self {
            Self {
                opcode: $opcode as u8,
                dest,
                src1,
                src2,
            }
        }
    };
}

impl Instruction {
    // Primitives
    instruction_builders!(load_const_i32, Opcode::LoadConstI32, dest, src1);
    instruction_builders!(load_const_i64, Opcode::LoadConstI64, dest, src1);
    instruction_builders!(load_const_f64, Opcode::LoadConstF64, dest, src1);

    // Heap
    instruction_builders!(alloc_string, Opcode::AllocString, dest, src1);
    instruction_builders!(alloc_array, Opcode::AllocArray, dest, src1);
    instruction_builders!(drop, Opcode::Drop, dest);

    // Array
    instruction_builders!(array_get, Opcode::ArrayGet, dest, src1, src2);
    instruction_builders!(array_set, Opcode::ArraySet, dest, src1, src2);
    instruction_builders!(array_len, Opcode::ArrayLen, dest, src1);

    // String
    instruction_builders!(string_concat, Opcode::StringConcat, dest, src1, src2);
    instruction_builders!(string_len, Opcode::StringLen, dest, src1);

    // General
    instruction_builders!(mov, Opcode::Move, dest, src1);

    // Control
    instruction_builders!(syscall, Opcode::SysCall, dest);
    instruction_builders!(jump, Opcode::Jump, dest);
    instruction_builders!(jump_zero, Opcode::JumpZero, dest, src1);

    // Arithmetic
    instruction_builders!(add_i32, Opcode::AddI32, dest, src1, src2);
    instruction_builders!(sub_i32, Opcode::SubI32, dest, src1, src2);
    instruction_builders!(mul_i32, Opcode::MulI32, dest, src1, src2);

    instruction_builders!(halt, Opcode::Halt);

    #[inline(always)]
    fn as_u32(self) -> u32 {
        ((self.opcode as u32) << 24)
            | ((self.dest as u32) << 16)
            | ((self.src1 as u32) << 8)
            | (self.src2 as u32)
    }
}

// Heap object types
#[derive(Debug, Clone)]
enum HeapObject {
    String(String),
    Array(Vec<u64>),
}

// Heap slot with generation tracking
#[derive(Debug)]
struct HeapSlot {
    object: Option<HeapObject>,
    generation: u32,
}

// Heap with generational indices
struct Heap {
    slots: Vec<HeapSlot>,
    free_list: Vec<usize>,
}

impl Heap {
    fn new() -> Self {
        Self {
            slots: Vec::new(),
            free_list: Vec::new(),
        }
    }

    fn alloc(&mut self, obj: HeapObject) -> u64 {
        let (index, generation) = if let Some(free_idx) = self.free_list.pop() {
            let slot = &mut self.slots[free_idx];
            slot.generation += 1;
            slot.object = Some(obj);
            (free_idx, slot.generation)
        } else {
            let index = self.slots.len();
            self.slots.push(HeapSlot {
                object: Some(obj),
                generation: 1,
            });
            (index, 1)
        };

        ((generation as u64) << 32) | (index as u64)
    }

    fn free(&mut self, handle: u64) -> Result<()> {
        let (index, generation) = Self::unpack_handle(handle);

        if index >= self.slots.len() {
            bail!("invalid heap index: {}", index);
        }

        let slot = &mut self.slots[index];

        if slot.generation != generation {
            bail!(
                "use-after-free detected! (generation mismatch: {} != {})",
                generation,
                slot.generation
            );
        }

        if slot.object.is_none() {
            bail!("double-free detected!");
        }

        slot.object = None;
        self.free_list.push(index);

        Ok(())
    }

    fn get(&self, handle: u64) -> Result<&HeapObject> {
        let (index, generation) = Self::unpack_handle(handle);

        if index >= self.slots.len() {
            bail!("invalid heap index: {}", index);
        }

        let slot = &self.slots[index];

        if slot.generation != generation {
            bail!(
                "use-after-free detected! (generation mismatch: {} != {})",
                generation,
                slot.generation
            );
        }

        slot.object
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("accessing freed object"))
    }

    fn get_mut(&mut self, handle: u64) -> Result<&mut HeapObject> {
        let (index, generation) = Self::unpack_handle(handle);

        if index >= self.slots.len() {
            bail!("invalid heap index: {}", index);
        }

        let slot = &mut self.slots[index];

        if slot.generation != generation {
            bail!(
                "use-after-free detected! (generation mismatch: {} != {})",
                generation,
                slot.generation
            );
        }

        slot.object
            .as_mut()
            .ok_or_else(|| anyhow::anyhow!("accessing freed object"))
    }

    #[inline(always)]
    fn unpack_handle(handle: u64) -> (usize, u32) {
        let index = (handle & 0xFFFF_FFFF) as usize;
        let generation = (handle >> 32) as u32;
        (index, generation)
    }

    fn is_handle(&self, val: u64) -> bool {
        let (index, generation) = Self::unpack_handle(val);
        if index >= self.slots.len() {
            return false;
        }
        let slot = &self.slots[index];
        slot.generation == generation && slot.object.is_some()
    }
}

struct ConstantPools<'a> {
    i32_pool: &'a [i32],
    i64_pool: &'a [i64],
    f64_pool: &'a [f64],
    string_pool: &'a [&'a str],
}

struct Vm<'a, W: Write> {
    registers: [u64; 16],
    code: &'a [u32],
    pools: ConstantPools<'a>,
    heap: Heap,
    out: W,
}

impl<'a, W: Write> Vm<'a, W> {
    fn new(code: &'a [u32], pools: ConstantPools<'a>, out: W) -> Self {
        Self {
            registers: [0; 16],
            code,
            pools,
            heap: Heap::new(),
            out,
        }
    }

    #[inline(always)]
    fn store_i32(&mut self, reg: usize, val: i32) {
        self.registers[reg] = val as i64 as u64;
    }

    #[inline(always)]
    fn load_i32(&self, reg: usize) -> i32 {
        self.registers[reg] as i64 as i32
    }

    #[inline(always)]
    fn store_i64(&mut self, reg: usize, val: i64) {
        self.registers[reg] = val as u64;
    }

    #[inline(always)]
    fn load_i64(&self, reg: usize) -> i64 {
        self.registers[reg] as i64
    }

    #[inline(always)]
    fn store_f64(&mut self, reg: usize, val: f64) {
        self.registers[reg] = val.to_bits();
    }

    #[inline(always)]
    fn load_f64(&self, reg: usize) -> f64 {
        f64::from_bits(self.registers[reg])
    }

    #[inline(always)]
    fn store_handle(&mut self, reg: usize, handle: u64) {
        self.registers[reg] = handle;
    }

    #[inline(always)]
    fn load_handle(&self, reg: usize) -> u64 {
        self.registers[reg]
    }

    fn dispatch(&mut self, ip: usize) -> Result<()> {
        let raw = unsafe { *self.code.get_unchecked(ip) };
        let opcode = (raw >> 24) as u8;
        let dest = ((raw >> 16) & 0xFF) as usize;
        let src1 = ((raw >> 8) & 0xFF) as usize;
        let src2 = (raw & 0xFF) as usize;

        match opcode {
            0x01 => {
                // LoadConstI32
                let val = unsafe { *self.pools.i32_pool.get_unchecked(src1) };
                self.store_i32(dest, val);
                become self.dispatch(ip + 1)
            }
            0x02 => {
                // LoadConstI64
                let val = unsafe { *self.pools.i64_pool.get_unchecked(src1) };
                self.store_i64(dest, val);
                become self.dispatch(ip + 1)
            }
            0x03 => {
                // LoadConstF64
                let val = unsafe { *self.pools.f64_pool.get_unchecked(src1) };
                self.store_f64(dest, val);
                become self.dispatch(ip + 1)
            }

            0x10 => {
                // AllocString
                let s = unsafe { *self.pools.string_pool.get_unchecked(src1) };
                let handle = self.heap.alloc(HeapObject::String(s.to_string()));
                self.store_handle(dest, handle);
                become self.dispatch(ip + 1)
            }
            0x11 => {
                // AllocArray
                let size = self.load_i32(src1) as usize;
                let handle = self.heap.alloc(HeapObject::Array(vec![0; size]));
                self.store_handle(dest, handle);
                become self.dispatch(ip + 1)
            }
            0x12 => {
                // Drop
                let handle = self.load_handle(dest);
                self.heap.free(handle)?;
                self.registers[dest] = 0;
                become self.dispatch(ip + 1)
            }

            0x13 => {
                // ArrayGet
                let arr_handle = self.load_handle(src1);
                let index = self.load_i32(src2) as usize;

                if let HeapObject::Array(arr) = self.heap.get(arr_handle)? {
                    if index >= arr.len() {
                        bail!("array index out of bounds: {}", index);
                    }
                    self.registers[dest] = arr[index];
                } else {
                    bail!("not an array");
                }
                become self.dispatch(ip + 1)
            }
            0x14 => {
                // ArraySet
                let arr_handle = self.load_handle(dest);
                let index = self.load_i32(src1) as usize;
                let value = self.registers[src2];

                if let HeapObject::Array(arr) = self.heap.get_mut(arr_handle)? {
                    if index >= arr.len() {
                        bail!("array index out of bounds: {}", index);
                    }
                    arr[index] = value;
                } else {
                    bail!("not an array");
                }
                become self.dispatch(ip + 1)
            }
            0x15 => {
                // ArrayLen
                let arr_handle = self.load_handle(src1);
                if let HeapObject::Array(arr) = self.heap.get(arr_handle)? {
                    self.store_i32(dest, arr.len() as i32);
                } else {
                    bail!("not an array");
                }
                become self.dispatch(ip + 1)
            }

            0x16 => {
                // StringConcat
                let h1 = self.load_handle(src1);
                let h2 = self.load_handle(src2);

                let s1 = if let HeapObject::String(s) = self.heap.get(h1)? {
                    s.clone()
                } else {
                    bail!("not a string");
                };

                let s2 = if let HeapObject::String(s) = self.heap.get(h2)? {
                    s.clone()
                } else {
                    bail!("not a string");
                };

                let result = format!("{}{}", s1, s2);
                let handle = self.heap.alloc(HeapObject::String(result));
                self.store_handle(dest, handle);
                become self.dispatch(ip + 1)
            }
            0x17 => {
                // StringLen
                let h = self.load_handle(src1);
                if let HeapObject::String(s) = self.heap.get(h)? {
                    self.store_i32(dest, s.len() as i32);
                } else {
                    bail!("not a string");
                }
                become self.dispatch(ip + 1)
            }

            0x20 => {
                // Move
                self.registers[dest] = self.registers[src1];
                become self.dispatch(ip + 1)
            }

            0x30 => {
                // SysCall
                match dest as u8 {
                    0 => {
                        // Print - type-aware!
                        let val = self.registers[0];

                        // Check if it's a valid heap handle
                        if self.heap.is_handle(val) {
                            match self.heap.get(val)? {
                                HeapObject::String(s) => writeln!(self.out, "{}", s)?,
                                HeapObject::Array(arr) => writeln!(self.out, "{:?}", arr)?,
                            }
                        } else {
                            // Try as i32 first (most common)
                            let as_i32 = val as i64 as i32;
                            if (as_i32 as i64 as u64) == val {
                                writeln!(self.out, "{}", as_i32)?;
                            } else {
                                // Try as f64
                                let as_f64 = f64::from_bits(val);
                                if as_f64.is_finite() {
                                    writeln!(self.out, "{}", as_f64)?;
                                } else {
                                    // Raw value
                                    writeln!(self.out, "{}", val)?;
                                }
                            }
                        }
                        become self.dispatch(ip + 1)
                    }
                    _ => bail!("unknown syscall: {}", dest),
                }
            }
            0x31 => {
                // Jump
                become self.dispatch(dest)
            }
            0x32 => {
                // JumpZero
                if self.registers[dest] == 0 {
                    become self.dispatch(src1)
                } else {
                    become self.dispatch(ip + 1)
                }
            }

            0x40 => {
                // AddI32
                let a = self.load_i32(src1);
                let b = self.load_i32(src2);
                self.store_i32(dest, a.wrapping_add(b));
                become self.dispatch(ip + 1)
            }
            0x41 => {
                // SubI32
                let a = self.load_i32(src1);
                let b = self.load_i32(src2);
                self.store_i32(dest, a.wrapping_sub(b));
                become self.dispatch(ip + 1)
            }
            0x42 => {
                // MulI32
                let a = self.load_i32(src1);
                let b = self.load_i32(src2);
                self.store_i32(dest, a.wrapping_mul(b));
                become self.dispatch(ip + 1)
            }

            0xFF => Ok(()),
            _ => bail!("unknown opcode: 0x{:02X}", opcode),
        }
    }

    fn run(&mut self) -> Result<()> {
        self.dispatch(0)
    }
}

fn main() -> Result<()> {
    let i32_pool = [5, 10, 0, 1];
    let i64_pool = [];
    let f64_pool = [f64::consts::PI];
    let string_pool = ["Hello", "World", "Test"];

    let pools = ConstantPools {
        i32_pool: &i32_pool,
        i64_pool: &i64_pool,
        f64_pool: &f64_pool,
        string_pool: &string_pool,
    };

    let code = [
        // Test string allocation and concatenation
        Instruction::alloc_string(1, 0).as_u32(), // r1 = "Hello"
        Instruction::alloc_string(2, 1).as_u32(), // r2 = "World"
        Instruction::string_concat(3, 1, 2).as_u32(), // r3 = r1 + r2
        Instruction::mov(0, 3).as_u32(),          // r0 = r3
        Instruction::syscall(0).as_u32(),         // print r0
        // Free the concatenated string
        Instruction::drop(3).as_u32(), // drop r3
        // Test array
        Instruction::load_const_i32(5, 0).as_u32(), // r5 = 5
        Instruction::alloc_array(6, 5).as_u32(),    // r6 = array[5]
        Instruction::load_const_i32(7, 1).as_u32(), // r7 = 10
        Instruction::load_const_i32(8, 2).as_u32(), // r8 = 0 (index)
        Instruction::array_set(6, 8, 7).as_u32(),   // array[0] = 10
        Instruction::array_get(0, 6, 8).as_u32(),   // r0 = array[0]
        Instruction::syscall(0).as_u32(),           // print r0
        // Test f64
        Instruction::load_const_f64(9, 0).as_u32(), // r9 = 3.14159
        Instruction::mov(0, 9).as_u32(),            // r0 = r9
        Instruction::syscall(0).as_u32(),           // print r0
        // Clean up
        Instruction::drop(1).as_u32(), // drop "Hello"
        Instruction::drop(2).as_u32(), // drop "World"
        Instruction::drop(6).as_u32(), // drop array
        Instruction::halt().as_u32(),
    ];

    let mut stdout = std::io::stdout().lock();
    let mut vm = Vm::new(&code, pools, stdout);
    vm.run()?;

    Ok(())
}
