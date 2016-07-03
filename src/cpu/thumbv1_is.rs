//! THUMBv1 instruction set

use std::fmt;

use super::{Cpu, RegisterIndex};

pub fn execute(cpu: &mut Cpu, instruction: u16) {
    let instruction = Instruction(instruction);

    instruction.execute(cpu);
}

impl Instruction {
    /// We decode the instruction based on bits [15:6]. That gives us
    /// 1024 possibilities.
    fn opcode(self) -> u16 {
        self.0 >> 6
    }

    fn reg_0(self) -> RegisterIndex {
        let r = self.0 & 7;

        RegisterIndex(r as u32)
    }

    fn reg_3(self) -> RegisterIndex {
        let r = (self.0 >> 3) & 7;

        RegisterIndex(r as u32)
    }

    fn reg_8(self) -> RegisterIndex {
        let r = (self.0 >> 8) & 7;

        RegisterIndex(r as u32)
    }

    fn imm8(self) -> u32 {
        (self.0 & 0xff) as u32
    }

    fn imm5(self) -> u32 {
        ((self.0 >> 6) & 0x1f) as u32
    }

    fn signed_imm11(self) -> u32 {
        let offset = (self.0 & 0x7ff) as u32;

        // sign extend
        let offset = (offset << 21) as i32;

        (offset >> 21) as u32
    }

    fn b_imm_offset_11(self) -> u32 {
        (self.0 & 0x7ff) as u32
    }

    fn execute(self, cpu: &mut Cpu) {
        match self.opcode() {
            0x080...0x09f => self.op08x_mov_i(cpu),
            0x100         => self.op100_and(cpu),
            0x120...0x13f => self.op12x_ldr_pc(cpu),
            0x1a0...0x1bf => self.op1ax_ldr_ri5(cpu),
            0x3c0...0x3df => self.op3cx_bl_hi(cpu),
            0x3e0...0x3ff => self.op3ex_bl_lo(cpu),
            _ => self.unimplemented(cpu),
        }
    }

    fn unimplemented(self, _: &mut Cpu) {
        panic!("Unimplemented instruction {} ({:03x})",
               self,
               self.opcode());
    }

    fn op08x_mov_i(self, cpu: &mut Cpu) {
        let rd  = self.reg_8();
        let val = self.imm8();

        cpu.set_reg(rd, val);

        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op100_and(self, cpu: &mut Cpu) {
        let rd = self.reg_0();
        let rm = self.reg_3();

        let a = cpu.reg(rd);
        let b = cpu.reg(rm);

        let val = a & b;

        cpu.set_reg(rd, val);
        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op12x_ldr_pc(self, cpu: &mut Cpu) {
        let rd = self.reg_8();
        let offset = self.imm8() << 2;

        let base = cpu.reg(RegisterIndex(15)) & !3;

        let addr = base.wrapping_add(offset);

        let val = cpu.load32(addr);

        cpu.set_reg(rd, val);
    }

    fn op1ax_ldr_ri5(self, cpu: &mut Cpu) {
        let rd     = self.reg_0();
        let rn     = self.reg_3();
        let offset = self.imm5() << 2;

        let base = cpu.reg(rn);

        let addr = base.wrapping_add(offset);

        let val = cpu.load32(addr);

        cpu.set_reg(rd, val);
    }

    fn op3cx_bl_hi(self, cpu: &mut Cpu) {
        // This instruction is coded on two successive half words. The
        // reference manual says that it's implementation defined
        // whether interrupts can happen between the two
        // instructions. The behaviour as also unpredictable if the
        // pair is broken somehow. I'm not really sure how to handle
        // all the corner cases here, I'd need to run some tests to
        // figure out how the ARM7TDMI behaves exactly. This
        // implementation seems simple enough that it migh very well
        // be exactly how the real hardware handles it.
        let offset_hi = self.signed_imm11() << 12;

        // The offset is based on the value of the PC register during
        // the 1st instruction
        let partial_target = cpu.reg(RegisterIndex(15)).wrapping_add(offset_hi);

        // The partial target branch is stored in RL
        cpu.set_reg(RegisterIndex(14), partial_target)
    }

    fn op3ex_bl_lo(self, cpu: &mut Cpu) {
        let offset_lo = self.b_imm_offset_11() << 1;

        let target = cpu.reg(RegisterIndex(14)).wrapping_add(offset_lo);

        let ra = cpu.next_pc | 1;

        cpu.set_reg(RegisterIndex(14), ra);

        cpu.set_pc(target);
    }
}

/// Wrapper around a 16bit instruction word
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Instruction(u16);

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:04x}", self.0)
    }
}
