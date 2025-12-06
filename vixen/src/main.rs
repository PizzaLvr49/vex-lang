#![expect(incomplete_features, unused)]
#![feature(explicit_tail_calls)]
#![feature(trim_prefix_suffix)]

mod assembly;

use core::time;
use std::time::Instant;

use anyhow::{Result, bail};

use crate::assembly::{Assembler, Disassembler};

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

struct Vm<'a> {
    registers: [i32; 16],
    code: &'a [u32],
    pool: &'a [i32],
}

impl<'a> Vm<'a> {
    #[inline(always)]
    fn new(code: &'a [u32], pool: &'a [i32]) -> Self {
        Self {
            registers: [0; 16],
            code,
            pool,
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
    let source = r#"
        .const
            LOOP_MAX = 100000000
            INC = 3
            DEC = 1

        .code
            load_const r3, LOOP_MAX
        loop_start:
            add_const r0, r0, INC
            sub_const r3, r3, DEC
            jump_nz r3, loop_start
            syscall #0
            halt
        "#;

    let mut asm = Assembler::new();

    let (code, pool) = asm.assemble(source)?;

    let disasm = Disassembler::new(&code, &pool);
    println!("Assembled bytecode:\n{}", disasm.disassemble());

    println!("Output:");

    let mut vm = Vm::new(&code, &pool);
    let timer = Instant::now();
    vm.run()?;
    let time = timer.elapsed();

    println!("\nTook: {:?} to run {} loops", time, pool[0]);

    Ok(())
}
