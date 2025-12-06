#![expect(incomplete_features, unused)]
#![feature(explicit_tail_calls)]
#![feature(trim_prefix_suffix)]

use std::{
    io::{self, Write},
    time::Instant,
};

use anyhow::{Result, bail};

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
enum Opcode {
    // Data
    LoadConst = 0x01,
    LoadImm = 0x02,
    Move = 0x05,

    // Control flow
    SysCall = 0x10,
    Jump = 0x11,
    JumpZero = 0x12,
    JumpNotZero = 0x13,
    ForNPrep = 0x14,
    ForNLoop = 0x15,

    // Arithmetic
    AddI32 = 0x20,
    SubI32 = 0x21,
    MulI32 = 0x22,
    DivI32 = 0x23,

    // Const Arithmetic
    AddConst = 0x28,
    SubConst = 0x29,
    MulConst = 0x30,
    DivConst = 0x31,

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

    ($name:ident, $opcode:expr, reg, imm16) => {
        #[inline(always)]
        fn $name(reg: u8, imm: i16) -> Self {
            let unsigned = imm as u16;
            Self {
                opcode: $opcode as u8,
                dest: reg,
                src1: (unsigned >> 8) as u8,
                src2: (unsigned & 0xFF) as u8,
            }
        }
    };

    ($name:ident, $opcode:expr, dest_imm, imm16) => {
        #[inline(always)]
        fn $name(dest: u8, imm: i16) -> Self {
            let unsigned = imm as u16;
            Self {
                opcode: $opcode as u8,
                dest,
                src1: (unsigned >> 8) as u8,
                src2: (unsigned & 0xFF) as u8,
            }
        }
    };

    ($name:ident, $opcode:expr, dest_src_const) => {
        #[inline(always)]
        fn $name(dest: u8, src: u8, pool_idx: u8) -> Self {
            Self {
                opcode: $opcode as u8,
                dest,
                src1: src,
                src2: pool_idx,
            }
        }
    };

    ($name:ident, $opcode:expr, reg, target) => {
        #[inline(always)]
        fn $name(reg: u8, target: u8) -> Self {
            Self {
                opcode: $opcode as u8,
                dest: reg,
                src1: target,
                src2: 0,
            }
        }
    };
}

impl Instruction {
    instruction_builders!(load_const, Opcode::LoadConst, dest, src1);
    instruction_builders!(mov, Opcode::Move, dest, src1);
    instruction_builders!(load_imm, Opcode::LoadImm, reg, imm16);

    instruction_builders!(add, Opcode::AddI32, dest, src1, src2);
    instruction_builders!(sub, Opcode::SubI32, dest, src1, src2);
    instruction_builders!(mul, Opcode::MulI32, dest, src1, src2);
    instruction_builders!(div, Opcode::DivI32, dest, src1, src2);

    instruction_builders!(add_const, Opcode::AddConst, dest_src_const);
    instruction_builders!(sub_const, Opcode::SubConst, dest_src_const);
    instruction_builders!(mul_const, Opcode::MulConst, dest_src_const);
    instruction_builders!(div_const, Opcode::DivConst, dest_src_const);

    instruction_builders!(jump, Opcode::Jump, dest);
    instruction_builders!(jump_zero, Opcode::JumpZero, reg, target);
    instruction_builders!(jump_nz, Opcode::JumpNotZero, reg, target);
    instruction_builders!(for_n_prep, Opcode::ForNPrep, reg, target);
    instruction_builders!(for_n_loop, Opcode::ForNLoop, reg, target);
    instruction_builders!(syscall, Opcode::SysCall, dest);
    instruction_builders!(halt, Opcode::Halt);

    #[inline(always)]
    fn as_u32(self) -> u32 {
        self.into()
    }
}

impl From<Instruction> for u32 {
    #[inline(always)]
    fn from(instr: Instruction) -> Self {
        ((instr.opcode as u32) << 24)
            | ((instr.dest as u32) << 16)
            | ((instr.src1 as u32) << 8)
            | (instr.src2 as u32)
    }
}

impl From<u32> for Instruction {
    #[inline(always)]
    fn from(value: u32) -> Self {
        Instruction {
            opcode: ((value >> 24) & 0xFF) as u8,
            dest: ((value >> 16) & 0xFF) as u8,
            src1: ((value >> 8) & 0xFF) as u8,
            src2: (value & 0xFF) as u8,
        }
    }
}

struct Vm<'a, W: Write> {
    registers: [i32; 16],
    code: &'a [u32],
    pool: &'a [i32],
    out: W,
}

impl<'a, W: Write> Vm<'a, W> {
    #[inline(always)]
    fn new(code: &'a [u32], pool: &'a [i32], out: W) -> Self {
        Self {
            registers: [0; 16],
            code,
            pool,
            out,
        }
    }

    #[inline(always)]
    fn dispatch(&mut self, ip: usize) -> Result<()> {
        let raw = unsafe { *self.code.get_unchecked(ip) };
        let opcode = (raw >> 24) as u8;
        let dest = ((raw >> 16) & 0xFF) as usize;
        let src1 = ((raw >> 8) & 0xFF) as usize;
        let src2 = (raw & 0xFF) as usize;

        match opcode {
            0x01 => {
                // LoadConst
                self.registers[dest] = unsafe { *self.pool.get_unchecked(src1) };
                become self.dispatch(ip + 1)
            }
            0x02 => {
                // LoadImm
                let unsigned = ((src1 as u16) << 8) | (src2 as u16);
                self.registers[dest] = unsigned as i16 as i32;
                become self.dispatch(ip + 1)
            }
            0x05 => {
                // Move
                let val = unsafe { *self.registers.get_unchecked(src1) };
                unsafe { *self.registers.get_unchecked_mut(dest) = val };
                become self.dispatch(ip + 1)
            }
            0x10 => {
                // SysCall
                match dest as u8 {
                    0 => {
                        println!("{}", self.registers[0]);
                        become self.dispatch(ip + 1)
                    }
                    _ => bail!("unknown syscall: {}", dest),
                }
            }
            0x11 => {
                // Jump
                become self.dispatch(dest)
            }
            0x12 => {
                // JumpZero
                let val = unsafe { *self.registers.get_unchecked(dest) };
                if val == 0 {
                    become self.dispatch(src1)
                } else {
                    become self.dispatch(ip + 1)
                }
            }
            0x13 => {
                // JumpNotZero
                let val = unsafe { *self.registers.get_unchecked(dest) };
                if val != 0 {
                    become self.dispatch(src1)
                } else {
                    become self.dispatch(ip + 1)
                }
            }
            0x14 => {
                // ForNPrep - dest = counter reg, src1 = loop body target
                // Initialize counter to 0 and jump to loop body
                unsafe { *self.registers.get_unchecked_mut(dest) = 0 };
                become self.dispatch(src1)
            }
            0x15 => {
                // ForNLoop - dest = counter reg, src1 = loop start target
                // Increment counter and jump back if not done
                let counter = unsafe { *self.registers.get_unchecked(dest) };
                let limit = unsafe { *self.registers.get_unchecked(dest + 1) };
                let new_counter = counter + 1;
                unsafe { *self.registers.get_unchecked_mut(dest) = new_counter };
                if new_counter < limit {
                    become self.dispatch(src1)
                } else {
                    become self.dispatch(ip + 1)
                }
            }
            0x20 => {
                // AddI32
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.registers.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_add(b) };
                become self.dispatch(ip + 1)
            }
            0x21 => {
                // SubI32
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.registers.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_sub(b) };
                become self.dispatch(ip + 1)
            }
            0x22 => {
                // MulI32
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.registers.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_mul(b) };
                become self.dispatch(ip + 1)
            }
            0x23 => {
                // DivI32
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.registers.get_unchecked(src2) };
                if b == 0 {
                    bail!("division by zero")
                }
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_div(b) };
                become self.dispatch(ip + 1)
            }
            0x28 => {
                // AddConst - dest = src1 + pool[src2]
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.pool.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_add(b) };
                become self.dispatch(ip + 1)
            }
            0x29 => {
                // SubConst - dest = src1 - pool[src2]
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.pool.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_sub(b) };
                become self.dispatch(ip + 1)
            }
            0x30 => {
                // MulConst - dest = src1 * pool[src2]
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.pool.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_mul(b) };
                become self.dispatch(ip + 1)
            }
            0x31 => {
                // DivConst - dest = src1 / pool[src2]
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.pool.get_unchecked(src2) };
                if b == 0 {
                    bail!("division by zero")
                }
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_div(b) };
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
    let pool = [10_000, 2, 0];

    let code = [
        // 0
        Instruction::load_const(3, 0).as_u32(), // r3 = 2
        // 1
        Instruction::load_const(0, 2).as_u32(), // r0 = 0
        // 2
        Instruction::load_const(4, 1).as_u32(), // r4 = 2
        // 3
        Instruction::for_n_prep(2, 4).as_u32(), // ???
        // 4
        Instruction::add(0, 0, 4).as_u32(), // r0 = r0 + r4
        // 5
        Instruction::syscall(0).as_u32(), // print r0
        // 6
        Instruction::for_n_loop(2, 4).as_u32(), // ???
        // 7
        Instruction::halt().as_u32(), // halt
    ];

    println!("Output:");

    let mut stdout = io::stdout().lock();

    let mut vm = Vm::new(&code, &pool, stdout);
    let timer = Instant::now();
    vm.run()?;
    let time = timer.elapsed();

    println!("\nTook: {:?} to print {} times", time, pool[0]);

    Ok(())
}
