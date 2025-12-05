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
    ip: usize,
    code: &'a [u32],
    pool: &'a [i32],
}

impl<'a> Vm<'a> {
    #[inline(always)]
    fn new(code: &'a [u32], pool: &'a [i32]) -> Self {
        Self {
            registers: [0; 16],
            ip: 0,
            code,
            pool,
        }
    }

    #[inline(always)]
    fn load_const(&mut self, dest: usize, idx: usize) {
        self.registers[dest] = self.pool[idx];
    }

    #[inline(always)]
    fn add_i32(&mut self, dest: usize, src1: usize, src2: usize) {
        self.registers[dest] = self.registers[src1] + self.registers[src2];
    }

    #[inline(always)]
    fn sub_i32(&mut self, dest: usize, src1: usize, src2: usize) {
        self.registers[dest] = self.registers[src1] - self.registers[src2];
    }

    #[inline(always)]
    fn mul_i32(&mut self, dest: usize, src1: usize, src2: usize) {
        self.registers[dest] = self.registers[src1] * self.registers[src2];
    }

    #[inline(always)]
    fn mov(&mut self, dest: usize, src1: usize) {
        self.registers[dest] = self.registers[src1];
    }

    #[inline(always)]
    fn syscall(&mut self, id: u8) -> Result<()> {
        match id {
            0 => {
                println!("{}", self.registers[0]);
                Ok(())
            }
            _ => bail!("unknown syscall"),
        }
    }

    fn run(&mut self) -> Result<()> {
        while self.ip < self.code.len() {
            let instr: Instruction = self.code[self.ip].into();
            self.ip += 1;

            match instr.opcode {
                x if x == Opcode::LoadConst as u8 => {
                    self.load_const(instr.dest as usize, instr.src1 as usize)
                }
                x if x == Opcode::AddI32 as u8 => self.add_i32(
                    instr.dest as usize,
                    instr.src1 as usize,
                    instr.src2 as usize,
                ),
                x if x == Opcode::SubI32 as u8 => self.sub_i32(
                    instr.dest as usize,
                    instr.src1 as usize,
                    instr.src2 as usize,
                ),
                x if x == Opcode::MulI32 as u8 => self.mul_i32(
                    instr.dest as usize,
                    instr.src1 as usize,
                    instr.src2 as usize,
                ),
                x if x == Opcode::Move as u8 => self.mov(instr.dest as usize, instr.src1 as usize),
                x if x == Opcode::SysCall as u8 => self.syscall(instr.dest)?,
                x if x == Opcode::Halt as u8 => break,
                _ => bail!("unknown opcode"),
            }
        }
        Ok(())
    }
}

fn main() -> Result<()> {
    let pool = [1, 2];

    let code = [
        Instruction::load_const(1, 0).into(),
        Instruction::load_const(2, 1).into(),
        Instruction::add(0, 1, 2).into(),
        Instruction::syscall(0).into(),
    ];

    let mut vm = Vm::new(code.as_slice(), pool.as_slice());
    vm.run()?;

    Ok(())
}
