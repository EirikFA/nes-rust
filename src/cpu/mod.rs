use std::ops::Add;

use instruction::Opcode;

use crate::cpu::instruction::AddressingMode;

mod instruction;

const PRG_START: u16 = 0x8000;
const PRG_COUNTER_ADDR: u16 = 0xFFFC;

enum StatusFlag {
  Carry = 0b0000_0001,
  Zero = 0b0000_0010,
  InterruptDisable = 0b0000_0100,
  DecimalMode = 0b0000_1000,
  Break = 0b0001_0000,
  Overflow = 0b0100_0000,
  Negative = 0b1000_0000,
}

#[derive(PartialEq, Debug)]
pub struct StatusRegister(u8);

impl StatusRegister {
  fn get(&self, flag: StatusFlag) -> bool {
    self.0 & (flag as u8) != 0
  }

  fn set(&mut self, flag: StatusFlag) {
    self.0 |= flag as u8;
  }

  fn unset(&mut self, flag: StatusFlag) {
    self.0 &= !(flag as u8);
  }

  fn update(&mut self, flag: StatusFlag, set: bool) {
    if set {
      self.set(flag);
    } else {
      self.unset(flag);
    }
  }

  fn reset(&mut self) {
    self.0 = 0;
  }
}

pub struct CPU {
  pub pc: u16,
  pub acc: u8,
  pub reg_x: u8,
  pub reg_y: u8,
  pub status: StatusRegister,
  memory: [u8; 0xFFFF],
}

impl CPU {
  pub fn new() -> Self {
    CPU {
      pc: PRG_START,
      acc: 0,
      reg_x: 0,
      reg_y: 0,
      status: StatusRegister(0),
      memory: [0; 0xFFFF],
    }
  }

  fn read_curr(&self) -> u8 {
    self.mem_read(self.pc)
  }

  fn mem_read(&self, addr: u16) -> u8 {
    self.memory[addr as usize]
  }

  fn mem_write(&mut self, addr: u16, data: u8) {
    self.memory[addr as usize] = data;
  }

  fn mem_read16(&self, addr: u16) -> u16 {
    let bytes: [u8; 2] = [self.mem_read(addr), self.mem_read(addr + 1)];
    u16::from_le_bytes(bytes)
  }

  fn mem_write16(&mut self, addr: u16, data: u16) {
    let bytes: [u8; 2] = data.to_le_bytes();
    self.mem_write(addr, bytes[0]);
    self.mem_write(addr + 1, bytes[1]);
  }

  fn operand_addr(&self, mode: &AddressingMode) -> u16 {
    match mode {
      AddressingMode::Accumulator => {
        panic!("Accumulator addressing mode is not supported by this method")
      }
      AddressingMode::Immediate => self.pc,
      AddressingMode::ZeroPage => self.mem_read(self.pc) as u16,
      AddressingMode::ZeroPageX => self.mem_read(self.pc).wrapping_add(self.reg_x) as u16,
      AddressingMode::ZeroPageY => self.mem_read(self.pc).wrapping_add(self.reg_y) as u16,
      AddressingMode::Absolute => self.mem_read16(self.pc),
      AddressingMode::AbsoluteX => self.mem_read16(self.pc).wrapping_add(self.reg_x as u16),
      AddressingMode::AbsoluteY => self.mem_read16(self.pc).wrapping_add(self.reg_y as u16),
      AddressingMode::IndirectX => {
        let addr = self.mem_read(self.pc).wrapping_add(self.reg_x) as u16;
        self.mem_read16(addr)
      }
      AddressingMode::IndirectY => {
        let addr = self.mem_read(self.pc) as u16;
        self.mem_read16(addr).wrapping_add(self.reg_y as u16)
      }
    }
  }

  fn do_instr_addr(&mut self, mode: &AddressingMode, instr_fn: fn(&mut Self, u16)) {
    instr_fn(self, self.operand_addr(mode));
    self.pc += mode.len();
  }

  pub fn reset(&mut self) {
    self.acc = 0;
    self.reg_x = 0;
    self.reg_y = 0;
    self.status.reset();
    self.pc = self.mem_read16(PRG_COUNTER_ADDR);
  }

  pub fn load(&mut self, program: Vec<u8>) {
    self.memory[(PRG_START as usize)..(PRG_START as usize + program.len())]
      .copy_from_slice(&program);
    self.mem_write16(PRG_COUNTER_ADDR, PRG_START);
  }

  pub fn load_run(&mut self, program: Vec<u8>) {
    self.load(program);
    self.reset();
    self.run();
  }

  pub fn run(&mut self) {
    loop {
      let opcode = Opcode::from(self.read_curr());
      self.pc += 1;

      match opcode {
        Opcode::AND(mode) => self.do_instr_addr(&mode, Self::and),
        Opcode::ASL(AddressingMode::Accumulator) => self.asl_acc(),
        Opcode::ASL(mode) => self.do_instr_addr(&mode, Self::asl),
        Opcode::BCC => self.branch(!self.status.get(StatusFlag::Carry)),
        Opcode::BCS => self.branch(self.status.get(StatusFlag::Carry)),
        Opcode::BEQ => self.branch(self.status.get(StatusFlag::Zero)),
        Opcode::BIT(mode) => self.do_instr_addr(&mode, Self::bit),
        Opcode::BMI => self.branch(self.status.get(StatusFlag::Negative)),
        Opcode::BNE => self.branch(!self.status.get(StatusFlag::Zero)),
        Opcode::BPL => self.branch(!self.status.get(StatusFlag::Negative)),
        Opcode::BRK => break,
        Opcode::BVC => self.branch(!self.status.get(StatusFlag::Overflow)),
        Opcode::BVS => self.branch(self.status.get(StatusFlag::Overflow)),
        Opcode::CLC => self.status.unset(StatusFlag::Carry),
        Opcode::CLD => self.status.unset(StatusFlag::DecimalMode),
        Opcode::CLI => self.status.unset(StatusFlag::InterruptDisable),
        Opcode::CLV => self.status.unset(StatusFlag::Overflow),
        Opcode::CMP(mode) => self.compare(self.acc, self.operand_addr(&mode)),
        Opcode::CPX(mode) => self.compare(self.reg_x, self.operand_addr(&mode)),
        Opcode::CPY(mode) => self.compare(self.reg_y, self.operand_addr(&mode)),
        Opcode::INX => self.inx(),
        Opcode::LDA(mode) => self.do_instr_addr(&mode, Self::lda),
        Opcode::STA(mode) => self.do_instr_addr(&mode, Self::sta),
        Opcode::TAX => self.tax(),
      }
    }
  }

  fn update_negative_flag(&mut self, value: u8) {
    self
      .status
      .update(StatusFlag::Negative, value & 0b1000_0000 != 0);
  }

  fn update_zero_flag(&mut self, value: u8) {
    self.status.update(StatusFlag::Zero, value == 0);
  }

  fn update_nz_flags(&mut self, value: u8) {
    self.update_negative_flag(value);
    self.update_zero_flag(value);
  }

  fn set_acc(&mut self, value: u8) {
    self.acc = value;
    self.update_nz_flags(value);
  }

  fn branch(&mut self, condition: bool) {
    if condition {
      let offset = self.mem_read(self.pc) as i8;
      // Add one to skip the offset byte
      self.pc = self.pc.wrapping_add(1).wrapping_add(offset as u16);
    }
  }

  fn and(&mut self, addr: u16) {
    self.set_acc(self.acc & self.mem_read(addr));
  }

  fn asl_acc(&mut self) {
    self.status.update(StatusFlag::Carry, self.acc >> 7 == 1);
    self.set_acc(self.acc << 1);
  }

  fn asl(&mut self, addr: u16) {
    let mut value = self.mem_read(addr);
    self.status.update(StatusFlag::Carry, value >> 7 == 1);
    value = value << 1;
    self.mem_write(addr, value);
    self.update_nz_flags(value);
  }

  fn bit(&mut self, addr: u16) {
    let value = self.mem_read(addr);
    self.status.update(StatusFlag::Zero, self.acc & value == 0);
    self
      .status
      .update(StatusFlag::Overflow, value & 0b0100_0000 != 0);
    self.update_negative_flag(value);
  }

  fn compare(&mut self, reg: u8, addr: u16) {
    let value = self.mem_read(addr);
    self.status.update(StatusFlag::Carry, reg >= value);
    self.update_nz_flags(reg.wrapping_sub(value));
  }

  fn sta(&mut self, addr: u16) {
    self.mem_write(addr, self.acc);
  }

  fn lda(&mut self, addr: u16) {
    self.set_acc(self.mem_read(addr));
  }

  fn tax(&mut self) {
    self.reg_x = self.acc;
    self.update_nz_flags(self.reg_x);
  }

  fn inx(&mut self) {
    self.reg_x = self.reg_x.wrapping_add(1);
    self.update_nz_flags(self.reg_x);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn branch_bcc() {
    let mut cpu = CPU::new();
    cpu.status.set(StatusFlag::Carry);
    cpu.load_run(vec![0x90, 0x05, 0x00]);
    assert_eq!(cpu.pc, PRG_START + 2 + 5 + 1);
  }

  #[test]
  fn lda_immediate() {
    let mut cpu = CPU::new();
    cpu.load_run(vec![0xA9, 0x05, 0x00]);
    assert_eq!(cpu.acc, 0x05);
    assert_eq!(cpu.status, StatusRegister(0));
  }

  #[test]
  fn lda_zero_page() {
    let mut cpu = CPU::new();
    cpu.mem_write(0x10, 0x55);
    cpu.load_run(vec![0xA5, 0x10, 0x00]);
    assert_eq!(cpu.acc, 0x55);
  }

  #[test]
  fn lda_sets_negative_zero_flags() {
    let mut cpu = CPU::new();
    cpu.load_run(vec![0xA9, 0x00, 0x00]);
    assert_eq!(cpu.status.get(StatusFlag::Zero), true);

    cpu.load_run(vec![0xA9, 0x81, 0x00]);
    assert_eq!(cpu.status.get(StatusFlag::Negative), true);
  }

  #[test]
  fn tax_sets_x() {
    let mut cpu = CPU::new();
    cpu.acc = 10;
    cpu.load(vec![0xAA, 0x00]);
    cpu.run();
    assert_eq!(cpu.reg_x, 10);
  }

  #[test]
  fn inx_overflows() {
    let mut cpu = CPU::new();
    cpu.reg_x = 0xFF;
    cpu.load(vec![0xE8, 0xE8, 0x00]);
    cpu.run();
    assert_eq!(cpu.reg_x, 1)
  }

  #[test]
  fn lda_tax_inx() {
    let mut cpu = CPU::new();
    cpu.load_run(vec![0xA9, 0xC0, 0xAA, 0xE8, 0x00]);
    assert_eq!(cpu.reg_x, 0xC1)
  }

  #[test]
  fn it_resets() {
    let mut cpu = CPU::new();
    cpu.acc = 10;
    cpu.reg_x = 20;
    cpu.reg_y = 30;
    cpu.status.set(StatusFlag::Negative);
    cpu.status.set(StatusFlag::Carry);
    cpu.pc = 50;
    cpu.reset();
    assert_eq!(cpu.acc, 0);
    assert_eq!(cpu.reg_x, 0);
    assert_eq!(cpu.reg_y, 0);
    assert_eq!(cpu.status, StatusRegister(0));
    assert_eq!(cpu.pc, cpu.mem_read16(PRG_COUNTER_ADDR));
  }
}
