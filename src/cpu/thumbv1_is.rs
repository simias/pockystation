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

    fn rm_full(self) -> RegisterIndex {
        let r = (self.0 >> 3) & 0xf;

        RegisterIndex(r as u32)
    }

    fn rd_full(self) -> RegisterIndex {
        let lo = (self.0 & 0x1f) as u32;
        let hi = ((self.0 >> 7) & 1) as u32;

        RegisterIndex((hi << 3) | lo)
    }

    fn imm8(self) -> u32 {
        (self.0 & 0xff) as u32
    }

    fn imm5(self) -> u32 {
        ((self.0 >> 6) & 0x1f) as u32
    }

    fn imm3(self) -> u32 {
        ((self.0 >> 6) & 7) as u32
    }

    fn signed_imm11(self) -> u32 {
        let offset = (self.0 & 0x7ff) as u32;

        // sign extend
        let offset = (offset << 21) as i32;

        (offset >> 21) as u32
    }

    fn signed_imm8(self) -> u32 {
        let offset = (self.0 & 0xff) as i8;

        // sign extend
        offset as u32
    }

    fn b_imm_offset_11(self) -> u32 {
        (self.0 & 0x7ff) as u32
    }

    fn register_list(self) -> u32 {
        (self.0 & 0xff) as u32
    }

    fn execute(self, cpu: &mut Cpu) {
        match self.opcode() {
            0x000...0x01f => self.op00x_lsl_ri5(cpu),
            0x078...0x07f => self.op07x_sub_i3(cpu),
            0x080...0x09f => self.op08x_mov_i(cpu),
            0x0a0...0x0bf => self.op0ax_cmp_i(cpu),
            0x100         => self.op100_and(cpu),
            0x102         => self.op102_lsl_r(cpu),
            0x108         => self.op108_tst(cpu),
            0x10c         => self.op10c_orr(cpu),
            0x10f         => self.op10f_mvn(cpu),
            0x118...0x11b => self.op118_cpy(cpu),
            0x11c | 0x11d => self.op11c_bx(cpu),
            0x120...0x13f => self.op12x_ldr_pc(cpu),
            0x180...0x19f => self.op18x_str_ri5(cpu),
            0x1a0...0x1bf => self.op1ax_ldr_ri5(cpu),
            0x1c0...0x1df => self.op1cx_strb_ri5(cpu),
            0x200...0x21f => self.op20x_strh_ri5(cpu),
            0x2d0...0x2d3 => self.op2d0_push(cpu),
            0x2d4...0x2d7 => self.op2d4_push_lr(cpu),
            0x2f0...0x2f3 => self.op2f0_pop(cpu),
            0x2f4...0x2f7 => self.op2f4_pop_pc(cpu),
            0x340...0x343 => self.op340_beq(cpu),
            0x344...0x347 => self.op344_bne(cpu),
            0x380...0x39f => self.op38x_b(cpu),
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

    fn op00x_lsl_ri5(self, cpu: &mut Cpu) {
        let rd     = self.reg_0();
        let rm     = self.reg_3();
        let shift  = self.imm5();

        let val = cpu.reg(rm);

        let val =
            match shift {
                0 => val,
                _ => {
                    let shifted = (val as u64) << shift;

                    let carry = (shifted & (1 << 32)) != 0;

                    cpu.set_c(carry);
                    shifted as u32
                }
            };

        cpu.set_reg(rd, val);
        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op07x_sub_i3(self, cpu: &mut Cpu) {
        let rd = self.reg_0();
        let rn = self.reg_3();
        let b  = self.imm3();

        let a = cpu.reg(rn);

        let val = a.wrapping_sub(b);

        let a_neg = (a as i32) < 0;
        let b_neg = (b as i32) < 0;
        let v_neg = (val as i32) < 0;

        cpu.set_reg(rd, val);
        cpu.set_n(v_neg);
        cpu.set_z(val == 0);
        cpu.set_c(a >= b);
        cpu.set_v((a_neg ^ b_neg) & (a_neg ^ v_neg));
    }

    fn op08x_mov_i(self, cpu: &mut Cpu) {
        let rd  = self.reg_8();
        let val = self.imm8();

        cpu.set_reg(rd, val);

        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op0ax_cmp_i(self, cpu: &mut Cpu) {
        let rn  = self.reg_8();
        let b   = self.imm8();

        let a = cpu.reg(rn);

        let val = a.wrapping_sub(b);

        let a_neg = (a as i32) < 0;
        let b_neg = (b as i32) < 0;
        let v_neg = (val as i32) < 0;

        cpu.set_n(v_neg);
        cpu.set_z(val == 0);
        cpu.set_c(a >= b);
        cpu.set_v((a_neg ^ b_neg) & (a_neg ^ v_neg));
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

    fn op102_lsl_r(self, cpu: &mut Cpu) {
        let rd = self.reg_0();
        let rs = self.reg_3();

        let shift = cpu.reg(rs);

        let val = cpu.reg(rd);

        let val =
            match shift {
                0 => val,
                1...31 => {
                    let shifted = (val as u64) << shift;

                    let carry = (shifted & (1 << 32)) != 0;

                    cpu.set_c(carry);
                    shifted as u32
                }
                32 => {
                    cpu.set_c((val & 1) != 0);

                    0
                }
                _ => {
                    cpu.set_c(false);

                    0
                }
            };

        cpu.set_reg(rd, val);
        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op108_tst(self, cpu: &mut Cpu) {
        let rn = self.reg_0();
        let rm = self.reg_3();

        let a = cpu.reg(rn);
        let b = cpu.reg(rm);

        let val = a & b;

        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op10c_orr(self, cpu: &mut Cpu) {
        let rd = self.reg_0();
        let rm = self.reg_3();

        let a = cpu.reg(rd);
        let b = cpu.reg(rm);

        let val = a | b;

        cpu.set_reg(rd, val);
        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op10f_mvn(self, cpu: &mut Cpu) {
        let rd = self.reg_0();
        let rm = self.reg_3();

        let val = !cpu.reg(rm);

        cpu.set_reg(rd, val);
        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
    }

    fn op11c_bx(self, cpu: &mut Cpu) {
        let rm = self.rm_full();

        if (self.0 & 7) != 0 {
            // Should be 0
            panic!("Invalid BX instruction {}", self);
        }

        let target = cpu.reg(rm);

        let thumb = (target & 1) != 0;

        cpu.set_pc_thumb(target & !1, thumb);
    }

    /// Also known as MOV(3)
    fn op118_cpy(self, cpu: &mut Cpu) {
        let rm = self.rm_full();
        let rd = self.rd_full();

        let val = cpu.reg(rm);

        cpu.set_reg(rd, val);
    }

    fn op12x_ldr_pc(self, cpu: &mut Cpu) {
        let rd = self.reg_8();
        let offset = self.imm8() << 2;

        let base = cpu.reg(RegisterIndex(15)) & !3;

        let addr = base.wrapping_add(offset);

        let val = cpu.load32(addr);

        cpu.set_reg(rd, val);
    }

    fn op18x_str_ri5(self, cpu: &mut Cpu) {
        let rd     = self.reg_0();
        let rn     = self.reg_3();
        let offset = self.imm5() << 2;

        let base = cpu.reg(rn);

        let addr = base.wrapping_add(offset);

        let val = cpu.reg(rd);

        cpu.store32(addr, val);
    }

    fn op2d0_push(self, cpu: &mut Cpu) {
        let list = self.register_list();

        // Push are SP-relative
        let sp = RegisterIndex(13);

        let num_regs = list.count_ones();

        if num_regs == 0 {
            panic!("Unpredictable PUSH {}", self);
        }

        let start_addr = cpu.reg(sp).wrapping_sub(4 * num_regs);

        let mut addr = start_addr;

        for i in 0..8 {
            if ((list >> i) & 1) != 0 {
                let reg = RegisterIndex(i);

                let val = cpu.reg(reg);
                cpu.store32(addr, val);

                addr = addr.wrapping_add(4);
            }
        }

        cpu.set_reg(sp, start_addr);
    }

    fn op2d4_push_lr(self, cpu: &mut Cpu) {
        let list = self.register_list();

        // Push are SP-relative
        let sp = RegisterIndex(13);

        // Register list + LR
        let num_regs = list.count_ones() + 1;

        let start_addr = cpu.reg(sp).wrapping_sub(4 * num_regs);

        let mut addr = start_addr;

        for i in 0..8 {
            if ((list >> i) & 1) != 0 {
                let reg = RegisterIndex(i);

                let val = cpu.reg(reg);
                cpu.store32(addr, val);

                addr = addr.wrapping_add(4);
            }
        }

        // Push LR
        let lr = cpu.reg(RegisterIndex(14));
        cpu.store32(addr, lr);

        cpu.set_reg(sp, start_addr);
    }

    fn op2f0_pop(self, cpu: &mut Cpu) {
        let list = self.register_list();

        // Pop are SP-relative
        let sp = RegisterIndex(13);

        let num_regs = list.count_ones();

        if num_regs == 0 {
            panic!("Unpredictable PUSH {}", self);
        }

        let mut addr = cpu.reg(sp);

        for i in 0..8 {
            if ((list >> i) & 1) != 0 {
                let reg = RegisterIndex(i);

                let val = cpu.load32(addr);

                cpu.set_reg(reg, val);

                addr = addr.wrapping_add(4);
            }
        }

        cpu.set_reg(sp, addr);
    }

    fn op2f4_pop_pc(self, cpu: &mut Cpu) {
        let list = self.register_list();

        // Pop are SP-relative
        let sp = RegisterIndex(13);

        let mut addr = cpu.reg(sp);

        for i in 0..8 {
            if ((list >> i) & 1) != 0 {
                let reg = RegisterIndex(i);

                let val = cpu.load32(addr);

                cpu.set_reg(reg, val);

                addr = addr.wrapping_add(4);
            }
        }

        // Load PC
        let pc = cpu.load32(addr);
        cpu.set_pc(pc & !1);
        addr = addr.wrapping_add(4);

        cpu.set_reg(sp, addr);
    }

    fn op340_beq(self, cpu: &mut Cpu) {
        let offset = self.signed_imm8() << 1;

        if cpu.z() {
            let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

            cpu.set_pc(pc);
        }
    }

    fn op344_bne(self, cpu: &mut Cpu) {
        let offset = self.signed_imm8() << 1;

        if !cpu.z() {
            let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

            cpu.set_pc(pc);
        }
    }

    fn op38x_b(self, cpu: &mut Cpu) {
        let offset = self.signed_imm11() << 1;

        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
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

    fn op1cx_strb_ri5(self, cpu: &mut Cpu) {
        let rd     = self.reg_0();
        let rn     = self.reg_3();
        let offset = self.imm5();

        let addr = cpu.reg(rn).wrapping_add(offset);

        let val = cpu.reg(rd);

        cpu.store8(addr, val);
    }

    fn op20x_strh_ri5(self, cpu: &mut Cpu) {
        let rd     = self.reg_0();
        let rn     = self.reg_3();
        let offset = self.imm5() << 1;

        let addr = cpu.reg(rn).wrapping_add(offset);

        if (addr & 1) != 0 {
            panic!("Unpredictable STRH");
        }

        let val = cpu.reg(rd);

        cpu.store16(addr, val);
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
