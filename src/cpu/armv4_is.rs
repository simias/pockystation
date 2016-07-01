//! ARMv4 instruction set

use std::fmt;

use super::{Cpu, RegisterIndex};

pub fn execute(cpu: &mut Cpu, instruction: u32) {
    let instruction = Instruction(instruction);

    instruction.execute(cpu);
}

/// Wrapper around a 32bit instruction word
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Instruction(u32);

impl Instruction {
    fn condition_code(self) -> u32 {
        self.0 >> 28
    }

    /// We use a LUT to decode the instruction based on bits [27:20]
    /// and [7:4]. That gives us 4096 possibilities.
    fn opcode(self) -> u32 {
        let opcode_hi = (self.0 >> 20) & 0xff;
        let opcode_lo = (self.0 >> 4) & 0xf;

        (opcode_hi << 4) | opcode_lo
    }

    fn rd(self) -> RegisterIndex {
        RegisterIndex((self.0 >> 12) & 0xf)
    }

    fn rn(self) -> RegisterIndex {
        RegisterIndex((self.0 >> 16) & 0xf)
    }

    fn rm(self) -> RegisterIndex {
        RegisterIndex(self.0 & 0xf)
    }

    /// Addressing mode 1: 32bit immediate value
    fn mode1_imm(self, cpu: &Cpu) -> (u32, bool) {
        let rot = (self.0 >> 8) & 0xf;
        let imm = self.0 & 0xff;

        if rot == 0 {
            (imm, cpu.c())
        } else {
            // Rotation factor is multiplied by two
            let rot = rot << 1;

            let imm = imm.rotate_right(rot);

            let carry_out = (imm >> 31) & 1 == 1;

            (imm, carry_out)
        }
    }

    /// Addressing mode 1: 32bit immediate value. Used when shifter
    /// carry is not needed.
    fn mode1_imm_no_carry(self) -> u32 {
        let rot = (self.0 >> 8) & 0xf;
        let imm = self.0 & 0xff;

        // Rotation factor is multiplied by two
        let rot = rot << 1;

        imm.rotate_right(rot)
    }

    /// Addressing mode 1: Logicat shift left my immediate. Used when
    /// shifter carry is not needed.
    fn mode1_register_lshift_imm_no_carry(self, cpu: &Cpu) -> u32 {
        let shift = (self.0 >> 7) & 0x1f;
        let rm = self.rm();

        let val = cpu.reg(rm);

        val << shift
    }

    /// Addressing mode 2: immediate offset
    fn mode2_offset_imm(self) -> u32 {
        self.0 & 0xfff
    }

    fn branch_imm_offset(self) -> u32 {
        // offset must be sign-extented
        let offset = (self.0 << 8) as i32;

        // Offset must be multiplied by 4 so we only shift it down 6
        // places.
        (offset >> 6) as u32
    }

    fn msr_field_mask(self) -> u32 {
        (self.0 >> 16) & 0xf
    }

    /// Register list for load/store multiple.
    fn register_list(self) -> u32 {
        self.0 & 0xffff
    }

    /// Execute an STM instruction. Returns the address of the last
    /// store + 4.
    fn stm(self, cpu: &mut Cpu, start_addr: u32) -> u32 {
        let rn   = self.rn();
        let list = self.register_list();

        let first = true;

        let mut addr = start_addr;

        for i in 0..15 {
            if ((list >> i) & 1) != 0 {
                let reg = RegisterIndex(i);

                // If Rn is specified in the register_list and it's the
                // first entry then the original value is stored,
                // otherwise it's "unpredictable".
                if !first && reg == rn {
                    panic!("Unpredictable STM! {}", self);
                }

                let val = cpu.reg(reg);
                cpu.store32(addr, val);

                addr = addr.wrapping_add(4);
            }
        }

        if ((list >> 15) & 1) != 0 {
            // Implementation defined
            panic!("PC stored in STM");
        }

        addr
    }

    /// Execute this instruction
    fn execute(self, cpu: &mut Cpu) {
        let n = cpu.n();
        let z = cpu.z();
        let c = cpu.c();
        let v = cpu.v();

        // All ARM instructions have a 4bit "condition" code which can
        // be used to conditionally execute an instruction without
        // having to use a branch
        let cond_true =
            match self.condition_code() {
                // Equal (EQ)
                0b0000 => z,
                // Not equal (NE)
                0b0001 => !z,
                // Unsigned higher, or same (CS)
                0b0010 => c,
                // Unsigned lower (CC)
                0b0011 => !c,
                // Negative (MI)
                0b0100 => n,
                // Positive, or 0 (PL)
                0b0101 => !n,
                // Overflow (VS)
                0b0110 => v,
                // No overflow (VC)
                0b0111 => !v,
                // Unsigned higher (HI)
                0b1000 => c && !z,
                // Unsigned lower, or same (LS)
                0b1001 => !c || z,
                // Greater, or equal (GE)
                0b1010 => n == v,
                // Less than (LT)
                0b1011 => n != v,
                // Greater than (GT)
                0b1100 => !z && (n == v),
                // Less than, or equal (LE)
                0b1101 => z || (n != v),
                // Always (AL)
                0b1110 => true,
                // This condition code is "unpredictable".
                0b1111 => panic!("Unexpected ARM condition 0b1111"),
                _ => unreachable!(),
            };

        if cond_true {
            self.decode_and_execute(cpu);
        }
    }

    fn decode_and_execute(self, cpu: &mut Cpu) {
        match self.opcode() {
            0x000 | 0x008 => self.op000_and_lshift(cpu),
            0x120         => self.op120_msr_cpsr(cpu),
            0x121         => self.op121_bx(cpu),
            0x1a0 | 0x1a8 => self.op1a0_mov_lshift(cpu),
            0x240...0x24f => self.op24x_sub_i(cpu),
            0x310...0x31f => self.op31x_tst_i(cpu),
            0x350...0x35f => self.op35x_cmp_i(cpu),
            0x3a0...0x3af => self.op3ax_mov_i(cpu),
            0x580...0x58f => self.op58x_str_pu(cpu),
            0x590...0x59f => self.op59x_ldr_pu(cpu),
            0x5c0...0x5cf => self.op5cx_strb_pu(cpu),
            0x8a0...0x8af => self.op8ax_stm_uw(cpu),
            0x8b0...0x8bf => self.op8bx_ldm_uw(cpu),
            0x920...0x92f => self.op92x_stm_pw(cpu),
            0xa00...0xaff => self.opaxx_b(cpu),
            0xb00...0xbff => self.opbxx_bl(cpu),
            _             => self.unimplemented(cpu),
        }
    }

    fn unimplemented(self, _: &mut Cpu) {
        panic!("Unimplemented instruction {} ({:03x})",
               self,
               self.opcode());
    }

    fn op000_and_lshift(self, cpu: &mut Cpu) {
        let dst = self.rd();
        let rn  = self.rn();
        let and = self.mode1_register_lshift_imm_no_carry(cpu);

        let val = cpu.reg(rn) & and;

        cpu.set_reg(dst, val);
    }

    fn op120_msr_cpsr(self, cpu: &mut Cpu) {
        let rm   = self.rm();
        let mask = self.msr_field_mask();

        if (self.0 & 0xff00) != 0xf000 {
            panic!("Invalid MSR instruction {}", self);
        }

        let val = cpu.reg(rm);

        cpu.msr_cpsr(val, mask);
    }

    fn op121_bx(self, cpu: &mut Cpu) {
        let rm = self.rm();

        if (self.0 & 0xfff00) != 0xfff00 {
            // "should be one"
            panic!("Invalid BX instruction {}", self);
        }

        let target = cpu.reg(rm);

        println!("BX 0x{:08x}", target);

        // If bit 0 of the target is set we switch to Thumb mode
        let thumb = (target & 1) != 0;
        let address = target & !1;

        cpu.set_thumb(thumb);
        cpu.set_pc(address);
    }

    fn op1a0_mov_lshift(self, cpu: &mut Cpu) {
        let dst = self.rd();
        let val = self.mode1_register_lshift_imm_no_carry(cpu);

        cpu.set_reg(dst, val);
    }

    fn op24x_sub_i(self, cpu: &mut Cpu) {
        let dst = self.rd();
        let rn  = self.rn();
        let b   = self.mode1_imm_no_carry();

        let a = cpu.reg(rn);

        let val = a.wrapping_sub(b);

        cpu.set_reg(dst, val);
    }

    fn op31x_tst_i(self, cpu: &mut Cpu) {
        let rn       = self.rn();
        let rd       = self.rd();
        let (imm, c) = self.mode1_imm(cpu);

        if rd != RegisterIndex(0) {
            // "should be zero"
            panic!("TST instruction with non-0 Rd");
        }

        let val = cpu.reg(rn) & imm;

        cpu.set_n((val as i32) < 0);
        cpu.set_z(val == 0);
        cpu.set_c(c);
    }

    fn op35x_cmp_i(self, cpu: &mut Cpu) {
        let rn  = self.rn();
        let rd  = self.rd();
        let b   = self.mode1_imm_no_carry();

        if rd != RegisterIndex(0) {
            // "should be zero"
            panic!("CMP instruction with non-0 Rd");
        }

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

    fn op3ax_mov_i(self, cpu: &mut Cpu) {
        let dst = self.rd();
        let val = self.mode1_imm_no_carry();

        cpu.set_reg(dst, val);
    }

    fn op58x_str_pu(self, cpu: &mut Cpu) {
        let src    = self.rd();
        let base   = self.rn();
        let offset = self.mode2_offset_imm();

        if src.is_pc() {
            // Implementation defined
            panic!("PC stored in STR");
        }

        let addr = cpu.reg(base).wrapping_add(offset);

        let val = cpu.reg(src);

        cpu.store32(addr, val);
    }

    fn op59x_ldr_pu(self, cpu: &mut Cpu) {
        let dst    = self.rd();
        let base   = self.rn();
        let offset = self.mode2_offset_imm();

        let addr = cpu.reg(base).wrapping_add(offset);

        let val = cpu.load32(addr);

        cpu.set_reg_pc_mask(dst, val);
    }

    fn op5cx_strb_pu(self, cpu: &mut Cpu) {
        let src    = self.rd();
        let base   = self.rn();
        let offset = self.mode2_offset_imm();

        if src.is_pc() {
            // Unpredictable (not "implementation defined" like STR
            // for some reason)
            panic!("PC stored in STRB");
        }

        let addr = cpu.reg(base).wrapping_add(offset);

        let val = cpu.reg(src);

        cpu.store8(addr, val);
    }

    fn op8ax_stm_uw(self, cpu: &mut Cpu) {
        let rn = self.rn();

        if rn.is_pc() {
            panic!("PC-relative STM!");
        }

        let start_addr = cpu.reg(rn);

        let end_addr = self.stm(cpu, start_addr);

        cpu.set_reg(rn, end_addr);
    }

    fn op8bx_ldm_uw(self, cpu: &mut Cpu) {
        let rn   = self.rn();
        let list = self.register_list();

        if rn.is_pc() || (list & (1 << rn.0)) != 0 {
            // Can't load to the base register if we want writeback
            panic!("Unpredictable LDM");
        }

        let mut addr = cpu.reg(rn);

        for i in 0..16 {
            if ((list >> i) & 1) != 0 {
                let reg = RegisterIndex(i);

                let val = cpu.load32(addr);

                cpu.set_reg_pc_mask(reg, val);

                addr = addr.wrapping_add(4);
            }
        }

        cpu.set_reg(rn, addr);
    }

    fn op92x_stm_pw(self, cpu: &mut Cpu) {
        let rn   = self.rn();
        let list = self.register_list();

        if rn.is_pc() {
            // Using PC as base if we want writeback is unpredictable
            panic!("PC-relative STM!");
        }

        let num_regs = list.count_ones();

        let start_addr = cpu.reg(rn).wrapping_sub(4 * num_regs);

        cpu.set_reg(rn, start_addr);
    }

    fn opaxx_b(self, cpu: &mut Cpu) {
        let offset = self.branch_imm_offset();

        let pc = cpu.registers[15].wrapping_add(offset);

        cpu.set_pc(pc);
    }

    fn opbxx_bl(self, cpu: &mut Cpu) {
        let offset = self.branch_imm_offset();

        let pc = cpu.registers[15].wrapping_add(offset);

        let ra = cpu.next_pc;

        cpu.set_reg(RegisterIndex(14), ra);

        cpu.set_pc(pc);
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:08x}", self.0)
    }
}
