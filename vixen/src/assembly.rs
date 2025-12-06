use anyhow::{Context, Result, bail};
use std::collections::HashMap;

enum Section {
    None,
    Const,
    Code,
}

pub struct Assembler {
    code: Vec<u32>,
    pool: Vec<i32>,
    labels: HashMap<String, usize>,
    unresolved: Vec<(usize, String)>,
}

impl Assembler {
    pub fn new() -> Self {
        Self {
            code: Vec::new(),
            pool: Vec::new(),
            labels: HashMap::new(),
            unresolved: Vec::new(),
        }
    }

    pub fn add_const(&mut self, value: i32) -> u8 {
        if let Some(idx) = self.pool.iter().position(|&v| v == value) {
            return idx as u8;
        }
        let idx = self.pool.len();
        if idx > 255 {
            panic!("Constant pool overflow");
        }
        self.pool.push(value);
        idx as u8
    }

    pub fn assemble(&mut self, source: &str) -> Result<(Vec<u32>, Vec<i32>)> {
        let mut section = Section::None;

        for (line_num, raw) in source.lines().enumerate() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with(';') {
                continue;
            }

            if line.eq_ignore_ascii_case(".const") {
                section = Section::Const;
                continue;
            }
            if line.eq_ignore_ascii_case(".code") {
                section = Section::Code;
                continue;
            }

            match section {
                Section::Const => {
                    self.parse_const_line(line)
                        .with_context(|| format!("Line {}: {}", line_num + 1, line))?;
                }

                Section::Code => {
                    if line.ends_with(':') {
                        let name = line.trim_end_matches(':').to_string();
                        self.labels.insert(name, self.code.len());
                        continue;
                    }

                    let real = line.split(';').next().unwrap().trim();
                    if real.is_empty() {
                        continue;
                    }

                    self.parse_instruction(real)
                        .with_context(|| format!("Line {}: {}", line_num + 1, line))?;
                }

                Section::None => {
                    bail!("Line {}: content outside a section", line_num + 1);
                }
            }
        }

        for (idx, label) in &self.unresolved {
            let target = *self
                .labels
                .get(label)
                .ok_or_else(|| anyhow::anyhow!("Undefined label: {}", label))?;

            let old = self.code[*idx];
            let opcode = (old >> 24) as u8;
            let dest = ((old >> 16) & 0xFF) as u8;

            match opcode {
                0x11 => {
                    self.code[*idx] = Self::encode(opcode, target as u8, 0, 0);
                }
                0x12 | 0x13 => {
                    self.code[*idx] = Self::encode(opcode, dest, target as u8, 0);
                }
                _ => bail!("Invalid jump opcode"),
            }
        }

        Ok((self.code.clone(), self.pool.clone()))
    }

    fn parse_const_line(&mut self, line: &str) -> Result<()> {
        if let Some(eq) = line.find('=') {
            let name = line[..eq].trim().to_string();
            let val_str = line[eq + 1..].trim();
            let value: i32 = val_str
                .parse()
                .with_context(|| format!("Invalid const value: {}", val_str))?;

            let idx = self.add_const(value);
            self.labels.insert(name, idx as usize);
            return Ok(());
        }
        bail!("Invalid const declaration: {}", line)
    }

    fn parse_instruction(&mut self, line: &str) -> Result<()> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return Ok(());
        }

        let name = parts[0];
        let args = &parts[1..];

        match name {
            "load_const" => {
                let (r, c) = self.parse_reg_const(args)?;
                self.emit(0x01, r, c, 0);
            }
            "load_imm" => {
                let (r, imm) = self.parse_reg_imm(args)?;
                let u = imm as u16;
                self.emit(0x02, r, (u >> 8) as u8, (u & 0xFF) as u8);
            }
            "mov" | "move" => {
                let (d, s) = self.parse_two_regs(args)?;
                self.emit(0x05, d, s, 0);
            }
            "syscall" => {
                let id = self.parse_syscall_arg(args)?;
                self.emit(0x10, id, 0, 0);
            }

            "jump" | "jmp" => match self.parse_label_or_reg(args)? {
                LabelOrReg::Reg(r) => self.emit(0x11, r, 0, 0),
                LabelOrReg::Label(l) => {
                    self.unresolved.push((self.code.len(), l));
                    self.emit(0x11, 0, 0, 0);
                }
            },

            "jump_zero" | "jz" => {
                let (r, t) = self.parse_reg_label(args)?;
                match t {
                    LabelOrReg::Reg(rr) => self.emit(0x12, r, rr, 0),
                    LabelOrReg::Label(l) => {
                        self.unresolved.push((self.code.len(), l));
                        self.emit(0x12, r, 0, 0);
                    }
                }
            }

            "jump_nz" | "jnz" => {
                let (r, t) = self.parse_reg_label(args)?;
                match t {
                    LabelOrReg::Reg(rr) => self.emit(0x13, r, rr, 0),
                    LabelOrReg::Label(l) => {
                        self.unresolved.push((self.code.len(), l));
                        self.emit(0x13, r, 0, 0);
                    }
                }
            }

            "add" => {
                let (d, a, b) = self.parse_three_regs(args)?;
                self.emit(0x20, d, a, b);
            }
            "sub" => {
                let (d, a, b) = self.parse_three_regs(args)?;
                self.emit(0x21, d, a, b);
            }
            "mul" => {
                let (d, a, b) = self.parse_three_regs(args)?;
                self.emit(0x22, d, a, b);
            }
            "div" => {
                let (d, a, b) = self.parse_three_regs(args)?;
                self.emit(0x23, d, a, b);
            }

            "add_const" => {
                let (d, s, k) = self.parse_reg_reg_const(args)?;
                self.emit(0x28, d, s, k);
            }
            "sub_const" => {
                let (d, s, k) = self.parse_reg_reg_const(args)?;
                self.emit(0x29, d, s, k);
            }
            "mul_const" => {
                let (d, s, k) = self.parse_reg_reg_const(args)?;
                self.emit(0x30, d, s, k);
            }
            "div_const" => {
                let (d, s, k) = self.parse_reg_reg_const(args)?;
                self.emit(0x31, d, s, k);
            }

            "halt" => {
                self.emit(0xFF, 0, 0, 0);
            }

            _ => bail!("unknown instruction '{}'", name),
        }

        Ok(())
    }

    fn emit(&mut self, op: u8, d: u8, a: u8, b: u8) {
        self.code.push(Self::encode(op, d, a, b));
    }

    fn encode(op: u8, d: u8, a: u8, b: u8) -> u32 {
        ((op as u32) << 24) | ((d as u32) << 16) | ((a as u32) << 8) | (b as u32)
    }

    fn parse_register(&self, s: &str) -> Result<u8> {
        let s = s.trim().trim_end_matches(',');
        if !s.starts_with('r') {
            bail!("Expected register, got {}", s);
        }
        let n: u8 = s[1..].parse()?;
        Ok(n)
    }

    fn parse_id(&self, s: &str) -> Result<u8> {
        let s = s.trim().trim_prefix('#');

        let v: u8 = s.parse()?;
        Ok(v)
    }

    fn parse_constant_index(&self, s: &str) -> Result<u8> {
        let s = s.trim().trim_end_matches(',');

        if let Some(idx) = self.labels.get(s) {
            return Ok(*idx as u8);
        }

        let v: u8 = s.parse()?;
        Ok(v)
    }

    fn parse_two_regs(&self, args: &[&str]) -> Result<(u8, u8)> {
        if args.len() != 2 {
            bail!("Expected 2 args");
        }
        Ok((self.parse_register(args[0])?, self.parse_register(args[1])?))
    }

    fn parse_three_regs(&self, args: &[&str]) -> Result<(u8, u8, u8)> {
        if args.len() != 3 {
            bail!("Expected 3 args");
        }
        Ok((
            self.parse_register(args[0])?,
            self.parse_register(args[1])?,
            self.parse_register(args[2])?,
        ))
    }

    fn parse_reg_const(&self, args: &[&str]) -> Result<(u8, u8)> {
        if args.len() != 2 {
            bail!("Expected 2 args");
        }
        Ok((
            self.parse_register(args[0])?,
            self.parse_constant_index(args[1])?,
        ))
    }

    fn parse_reg_reg_const(&self, args: &[&str]) -> Result<(u8, u8, u8)> {
        if args.len() != 3 {
            bail!("Expected 3 args");
        }
        Ok((
            self.parse_register(args[0])?,
            self.parse_register(args[1])?,
            self.parse_constant_index(args[2])?,
        ))
    }

    fn parse_reg_imm(&self, args: &[&str]) -> Result<(u8, i16)> {
        if args.len() != 2 {
            bail!("Expected 2 args");
        }
        let imm: i16 = args[1].trim_end_matches(',').parse()?;
        Ok((self.parse_register(args[0])?, imm))
    }

    fn parse_syscall_arg(&self, args: &[&str]) -> Result<u8> {
        if args.len() != 1 {
            bail!("Expected 1 arg");
        }
        self.parse_id(args[0])
    }

    fn parse_label_or_reg(&self, args: &[&str]) -> Result<LabelOrReg> {
        if args.len() != 1 {
            bail!("Expected 1 arg");
        }

        let s = args[0].trim().trim_end_matches(',');
        if s.starts_with('r') {
            Ok(LabelOrReg::Reg(self.parse_register(s)?))
        } else {
            Ok(LabelOrReg::Label(s.to_string()))
        }
    }

    fn parse_reg_label(&self, args: &[&str]) -> Result<(u8, LabelOrReg)> {
        if args.len() != 2 {
            bail!("Expected 2 args");
        }
        let r = self.parse_register(args[0])?;
        Ok((r, self.parse_label_or_reg(&args[1..])?))
    }
}

enum LabelOrReg {
    Reg(u8),
    Label(String),
}

pub struct Disassembler<'a> {
    code: &'a [u32],
    pool: &'a [i32],
}

impl<'a> Disassembler<'a> {
    pub fn new(code: &'a [u32], pool: &'a [i32]) -> Self {
        Self { code, pool }
    }

    pub fn disassemble(&self) -> String {
        let mut out = String::new();

        out.push_str(&format!("; Constant Pool ({} entries):\n", self.pool.len()));
        for (i, &v) in self.pool.iter().enumerate() {
            out.push_str(&format!(";   K{}: {}\n", i, v));
        }
        out.push('\n');

        for (ip, &instr) in self.code.iter().enumerate() {
            let opcode = (instr >> 24) as u8;
            let dest = ((instr >> 16) & 0xFF) as u8;
            let src1 = ((instr >> 8) & 0xFF) as u8;
            let src2 = (instr & 0xFF) as u8;

            out.push_str(&format!("{:04}  ", ip));

            match opcode {
                0x01 => {
                    out.push_str(&format!("load_const r{}, k{}", dest, src1));
                }
                0x02 => {
                    let imm = (((src1 as u16) << 8) | (src2 as u16)) as i16;
                    out.push_str(&format!("load_imm r{}, {}", dest, imm));
                }
                0x05 => {
                    out.push_str(&format!("mov r{}, r{}", dest, src1));
                }
                0x10 => {
                    out.push_str(&format!("syscall #{}", dest));
                }
                0x11 => {
                    out.push_str(&format!("jump {}", dest));
                }
                0x12 => {
                    out.push_str(&format!("jump_zero r{}, {}", dest, src1));
                }
                0x13 => {
                    out.push_str(&format!("jump_nz r{}, {}", dest, src1));
                }
                0x20 => {
                    out.push_str(&format!("add r{}, r{}, r{}", dest, src1, src2));
                }
                0x21 => {
                    out.push_str(&format!("sub r{}, r{}, r{}", dest, src1, src2));
                }
                0x22 => {
                    out.push_str(&format!("mul r{}, r{}, r{}", dest, src1, src2));
                }
                0x23 => {
                    out.push_str(&format!("div r{}, r{}, r{}", dest, src1, src2));
                }
                0x28 => {
                    out.push_str(&format!("add_const r{}, r{}, k{}", dest, src1, src2));
                }
                0x29 => {
                    out.push_str(&format!("sub_const r{}, r{}, k{}", dest, src1, src2));
                }
                0x30 => {
                    out.push_str(&format!("mul_const r{}, r{}, k{}", dest, src1, src2));
                }
                0x31 => {
                    out.push_str(&format!("div_const r{}, r{}, k{}", dest, src1, src2));
                }
                0xFF => {
                    out.push_str("halt");
                }
                other => {
                    out.push_str(&format!("unknown 0x{:02X}", other));
                }
            }

            out.push('\n');
        }

        out
    }
}
