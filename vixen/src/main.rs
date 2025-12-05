#![expect(incomplete_features, unused)]
#![feature(explicit_tail_calls)]

use anyhow::{Result, bail};

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
enum Opcode {
    LoadConst = 0x01,
    AddI32 = 0x02,
    SubI32 = 0x03,
    MulI32 = 0x04,
    Move = 0x05,
    SysCall = 0x10,
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

impl Instruction {
    #[inline(always)]
    fn load_const(dest: u8, src1: u8) -> Self {
        Self {
            opcode: Opcode::LoadConst as u8,
            dest,
            src1,
            src2: 0,
        }
    }

    #[inline(always)]
    fn add(dest: u8, src1: u8, src2: u8) -> Self {
        Self {
            opcode: Opcode::AddI32 as u8,
            dest,
            src1,
            src2,
        }
    }

    #[inline(always)]
    fn sub(dest: u8, src1: u8, src2: u8) -> Self {
        Self {
            opcode: Opcode::SubI32 as u8,
            dest,
            src1,
            src2,
        }
    }

    #[inline(always)]
    fn mul(dest: u8, src1: u8, src2: u8) -> Self {
        Self {
            opcode: Opcode::MulI32 as u8,
            dest,
            src1,
            src2,
        }
    }

    #[inline(always)]
    fn mov(dest: u8, src1: u8) -> Self {
        Self {
            opcode: Opcode::Move as u8,
            dest,
            src1,
            src2: 0,
        }
    }

    #[inline(always)]
    fn syscall(id: u8) -> Self {
        Self {
            opcode: Opcode::SysCall as u8,
            dest: id,
            src1: 0,
            src2: 0,
        }
    }

    #[inline(always)]
    fn halt() -> Self {
        Self {
            opcode: Opcode::Halt as u8,
            dest: 0,
            src1: 0,
            src2: 0,
        }
    }

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
    fn dispatch(&mut self, mut ip: usize) -> Result<()> {
        if ip >= self.code.len() {
            return Ok(());
        }

        let raw = unsafe { *self.code.get_unchecked(ip) };
        let opcode = (raw >> 24) as u8;
        let dest = ((raw >> 16) & 0xFF) as usize;
        let src1 = ((raw >> 8) & 0xFF) as usize;
        let src2 = (raw & 0xFF) as usize;

        match opcode {
            0x01 => {
                ip += 1;
                self.registers[dest] = unsafe { *self.pool.get_unchecked(src1) };
                become self.dispatch(ip)
            }
            0x02 => {
                ip += 1;
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.registers.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_add(b) };
                become self.dispatch(ip)
            }
            0x03 => {
                ip += 1;
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.registers.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_sub(b) };
                become self.dispatch(ip)
            }
            0x04 => {
                ip += 1;
                let a = unsafe { *self.registers.get_unchecked(src1) };
                let b = unsafe { *self.registers.get_unchecked(src2) };
                unsafe { *self.registers.get_unchecked_mut(dest) = a.wrapping_mul(b) };
                become self.dispatch(ip)
            }
            0x05 => {
                ip += 1;
                let val = unsafe { *self.registers.get_unchecked(src1) };
                unsafe { *self.registers.get_unchecked_mut(dest) = val };
                become self.dispatch(ip)
            }
            0x10 => {
                ip += 1;
                match dest as u8 {
                    0 => {
                        println!("{}", self.registers[0]);
                        become self.dispatch(ip)
                    }
                    _ => bail!("unknown syscall: {}", dest),
                }
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
    let pool = [1, 2];

    let code = [
        Instruction::load_const(1, 0).as_u32(),
        Instruction::load_const(2, 1).as_u32(),
        Instruction::add(0, 1, 2).as_u32(),
        Instruction::syscall(0).as_u32(),
    ];

    let mut vm = Vm::new(code.as_slice(), pool.as_slice());
    vm.run()?;

    Ok(())
}
