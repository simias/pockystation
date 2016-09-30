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
    /// We decode the instruction based on bits [27:20] and
    /// [7:4]. That gives us 4096 possibilities.
    fn opcode(self) -> u32 {
        let opcode_hi = (self.0 >> 20) & 0xff;
        let opcode_lo = (self.0 >> 4) & 0xf;

        (opcode_hi << 4) | opcode_lo
    }

    fn condition_code(self) -> u32 {
        self.0 >> 28
    }

    fn rn(self) -> RegisterIndex {
        RegisterIndex((self.0 >> 16) & 0xf)
    }

    fn rd(self) -> RegisterIndex {
        RegisterIndex((self.0 >> 12) & 0xf)
    }

    fn rs(self) -> RegisterIndex {
        RegisterIndex((self.0 >> 8) & 0xf)
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

            let carry_out = (imm as i32) < 0;

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

    /// Addressing mode 1: Logical shift left by immediate.
    fn mode1_register_lshift_imm(self, cpu: &Cpu) -> (u32, bool) {
        let shift = (self.0 >> 7) & 0x1f;
        let rm    = self.rm();

        let val = cpu.reg(rm);

        match shift {
            0 => (val, cpu.c()),
            _ => {
                let carry = ((val << (shift - 1)) & 0x80000000) != 0;

                (val << shift, carry)
            }
        }
    }

    /// Addressing mode 1: Logical shift left by immediate. Used when
    /// shifter carry is not needed.
    fn mode1_register_lshift_imm_no_carry(self, cpu: &Cpu) -> u32 {
        let shift = (self.0 >> 7) & 0x1f;
        let rm    = self.rm();

        let val = cpu.reg(rm);

        val << shift
    }

    /// Addressing mode 1: Logical shift right by immediate.
    fn mode1_register_rshift_imm(self, cpu: &Cpu) -> (u32, bool) {
        let shift = (self.0 >> 7) & 0x1f;
        let rm    = self.rm();

        let val = cpu.reg(rm);

        match shift {
            // Shift 0 means shift by 32
            0 => (0, (val as i32) < 0),
            _ => {
                let carry = (val >> (shift - 1)) & 1 != 0;

                (val >> shift, carry)
            }
        }
    }

    /// Addressing mode 1: Logical shift right by immediate. Used when
    /// shifter carry is not needed.
    fn mode1_register_rshift_imm_no_carry(self, cpu: &Cpu) -> u32 {
        let shift = (self.0 >> 7) & 0x1f;
        let rm    = self.rm();

        let val = cpu.reg(rm);

        match shift {
            // Shift 0 means shift by 32
            0 => 0,
            _ => val >> shift
        }
    }

    /// Addressing mode 1: Logical shift right by immediate. Used when
    /// shifter carry is not needed.
    fn mode1_register_arshift_imm_no_carry(self, cpu: &Cpu) -> u32 {
        let shift = (self.0 >> 7) & 0x1f;
        let rm    = self.rm();

        let val = cpu.reg(rm) as i32;

        let val =
            match shift {
                // Shift 0 means shift by 32, which is like shifting
                // by 31 when using a signed value (i.e. the sign bit
                // is replicated all over the 32bits)
                0 => val >> 31,
                _ => val >> shift
            };

        val as u32
    }

    /// Addressing mode 1: Logical shift left by register. Used when
    /// shifter carry is not needed.
    fn mode1_register_lshift_reg_no_carry(self, cpu: &Cpu) -> u32 {
        let rm = self.rm();
        let rs = self.rs();

        let val = cpu.reg(rm);
        let shift = cpu.reg(rs);

        match shift {
            0...31 => val << shift,
            _ => 0,
        }
    }

    /// Addressing mode 1: Logical shift right by register. Used when
    /// shifter carry is not needed.
    fn mode1_register_rshift_reg_no_carry(self, cpu: &Cpu) -> u32 {
        let rm = self.rm();
        let rs = self.rs();

        let val = cpu.reg(rm);
        let shift = cpu.reg(rs);

        match shift {
            0...31 => val >> shift,
            _ => 0,
        }
    }

    /// Addressing mode 2: immediate offset
    fn mode2_offset_imm(self) -> u32 {
        self.0 & 0xfff
    }

    /// Addressing mode 2: Logical shift left by immediate
    fn mode2_register_lshift(self, cpu: &Cpu) -> u32 {
        let shift = (self.0 >> 7) & 0x1f;
        let rm    = self.rm();

        let val = cpu.reg(rm);

        val << shift
    }

    /// Addressing mode 3: Miscellaneous loads and stores - immediate
    /// offset
    fn mode3_imm_hl(self) -> u32 {
        let hi = (self.0 >> 8) & 0xf;
        let lo = self.0 & 0xf;

        (hi << 4) | lo
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

    /// Load a 32 bit value from memory and optionally rotate it based
    /// on bits [1:0]
    fn ldr(self, cpu: &mut Cpu, addr: u32) -> u32 {
        let rot = (addr & 3) * 8;
        let addr = addr & !3;

        let val = cpu.load32(addr);

        val.rotate_right(rot)
    }

    /// Execute an STM instruction. Returns the address of the last
    /// store + 4.
    fn stm(self, cpu: &mut Cpu, start_addr: u32) -> u32 {
        let rn   = self.rn();
        let list = self.register_list();

        let mut first = true;

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
                first = false;
            }
        }

        if ((list >> 15) & 1) != 0 {
            // Implementation defined
            panic!("PC stored in STM");
        }

        addr
    }

    fn subs(self, cpu: &mut Cpu, rd: RegisterIndex, a: u32, b: u32) {
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
        let handler = OPCODE_LUT[self.opcode() as usize];

        handler(self, cpu);
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x{:08x}", self.0)
    }
}

/// Addressing mode 1: Data-processing operands
trait DataAddressingMode {
    /// Return the value of the operand
    fn value(instruction: Instruction, cpu: &Cpu) -> u32;

    /// Return the value of the operand along with the ALU carry
    fn value_carry(instruction: Instruction, cpu: &Cpu) -> (u32, bool);

    /// Used to validate that the addressing mode matches the
    /// instruction (useful for debugging).
    fn is_valid(instruction: Instruction, opcode: u32, s: bool) -> bool;
}

struct Mode1Imm;

impl DataAddressingMode for Mode1Imm {
    fn value(instruction: Instruction, _: &Cpu) -> u32 {
        let rot = (instruction.0 >> 8) & 0xf;
        let imm = instruction.0 & 0xff;

        // Rotation factor is multiplied by two
        imm.rotate_right(rot)
    }

    fn value_carry(instruction: Instruction, cpu: &Cpu) -> (u32, bool) {
        let rot = (instruction.0 >> 8) & 0xf;
        let imm = instruction.0 & 0xff;

        if rot == 0 {
            (imm, cpu.c())
        } else {
            // Rotation factor is multiplied by two
            let rot = rot << 1;

            let imm = imm.rotate_right(rot);

            let carry_out = (imm as i32) < 0;

            (imm, carry_out)
        }
    }

    fn is_valid(instruction: Instruction, opcode: u32, s: bool) -> bool {
        ((instruction.0 >> 20) & 1) == s as u32 &&
            ((instruction.0 >> 21) & 0xf) == opcode &&
            ((instruction.0 >> 25) & 7) == 1
    }
}

struct Mode1LslImm;

impl DataAddressingMode for Mode1LslImm {
    fn value(instruction: Instruction, cpu: &Cpu) -> u32 {
        let shift = (instruction.0 >> 7) & 0x1f;
        let rm = instruction.rm();

        let val = cpu.reg(rm);

        val << shift
    }

    fn value_carry(instruction: Instruction, cpu: &Cpu) -> (u32, bool) {
        let shift = (instruction.0 >> 7) & 0x1f;
        let rm = instruction.rm();

        let val = cpu.reg(rm);

        match shift {
            0 => (val, cpu.c()),
            _ => {
                let carry = ((val << (shift - 1)) & 0x80000000) != 0;

                (val << shift, carry)
            }
        }
    }

    fn is_valid(instruction: Instruction, opcode: u32, s: bool) -> bool {
        ((instruction.0 >> 20) & 1) == s as u32 &&
            ((instruction.0 >> 21) & 0xf) == opcode &&
            ((instruction.0 >> 25) & 7) == 0 &&
            ((instruction.0 >> 4) & 7) == 0
    }
}

struct Mode1LsrImm;

impl DataAddressingMode for Mode1LsrImm {
    fn value(instruction: Instruction, cpu: &Cpu) -> u32 {
        let shift = (instruction.0 >> 7) & 0x1f;
        let rm    = instruction.rm();

        let val = cpu.reg(rm);

        match shift {
            // Shift 0 means shift by 32
            0 => 0,
            _ => val >> shift
        }
    }

    fn value_carry(instruction: Instruction, cpu: &Cpu) -> (u32, bool) {
        let shift = (instruction.0 >> 7) & 0x1f;
        let rm    = instruction.rm();

        let val = cpu.reg(rm);

        match shift {
            // Shift 0 means shift by 32
            0 => (0, (val as i32) < 0),
            _ => {
                let carry = (val >> (shift - 1)) & 1 != 0;

                (val >> shift, carry)
            }
        }
    }

    fn is_valid(instruction: Instruction, opcode: u32, s: bool) -> bool {
        ((instruction.0 >> 20) & 1) == s as u32 &&
            ((instruction.0 >> 21) & 0xf) == opcode &&
            ((instruction.0 >> 25) & 7) == 0 &&
            ((instruction.0 >> 4) & 7) == 0b010
    }
}

fn unimplemented(instruction: Instruction, cpu: &mut Cpu) {
    panic!("Unimplemented instruction {} ({:03x})\n{:?}",
           instruction,
           instruction.opcode(),
           cpu);
}

fn and<M>(instruction: Instruction, cpu: &mut Cpu)
    where M: DataAddressingMode {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let b = M::value(instruction, cpu);

    debug_assert!(M::is_valid(instruction, 0, false));

    let a = cpu.reg(rn);

    let val = a & b;

    cpu.set_reg(rd, val);
}

fn ands<M>(instruction: Instruction, cpu: &mut Cpu)
    where M: DataAddressingMode {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let (b, carry) = M::value_carry(instruction, cpu);

    debug_assert!(M::is_valid(instruction, 0, true));

    let a = cpu.reg(rn);

    let val = a & b;

    cpu.set_reg(rd, val);

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
    cpu.set_c(carry);
}

fn eor<M>(instruction: Instruction, cpu: &mut Cpu)
    where M: DataAddressingMode {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let b  = M::value(instruction, cpu);

    debug_assert!(M::is_valid(instruction, 1, false));

    let a = cpu.reg(rn);

    let val = a ^ b;

    cpu.set_reg(rd, val);
}

fn sub<M>(instruction: Instruction, cpu: &mut Cpu)
    where M: DataAddressingMode {
    let dst = instruction.rd();
    let rn  = instruction.rn();
    let b   = M::value(instruction, cpu);

    debug_assert!(M::is_valid(instruction, 2, false));

    let a = cpu.reg(rn);

    let val = a.wrapping_sub(b);

    cpu.set_reg(dst, val);
}

fn subs<M>(instruction: Instruction, cpu: &mut Cpu)
    where M: DataAddressingMode {
    let rd  = instruction.rd();
    let rn  = instruction.rn();
    let b   = M::value(instruction, cpu);

    debug_assert!(M::is_valid(instruction, 2, true));

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


fn op080_add_lsl_i(instruction: Instruction, cpu: &mut Cpu) {
    let dst = instruction.rd();
    let rn  = instruction.rn();
    let b   = instruction.mode1_register_lshift_imm_no_carry(cpu);

    let a = cpu.reg(rn);

    let val = a.wrapping_add(b);

    cpu.set_reg(dst, val);
}

fn mul(instruction: Instruction, cpu: &mut Cpu) {
    let rm  = instruction.rm();
    let rs  = instruction.rs();
    let rn  = instruction.rn();

    if (instruction.0 & 0xf000) != 0 {
        // Should be 0
        panic!("Invalid MUL instruction");
    }

    let val = cpu.reg(rm).wrapping_mul(cpu.reg(rs));

    cpu.set_reg(rn, val);
}

fn op100_mrs_cpsr(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();

    if (instruction.0 & 0xf0fff) != 0xf0000 {
        panic!("Invalid MRS instruction {}", instruction);
    }

    let cpsr = cpu.cpsr();

    cpu.set_reg(rd, cpsr);
}

fn op110_tst_lsl_i(instruction: Instruction, cpu: &mut Cpu) {
    let rn       = instruction.rn();
    let rd       = instruction.rd();
    let (imm, c) = instruction.mode1_register_lshift_imm(cpu);

    if rd != RegisterIndex(0) {
        // "should be zero"
        panic!("TST instruction with non-0 Rd");
    }

    let val = cpu.reg(rn) & imm;

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
    cpu.set_c(c);
}

fn op120_msr_cpsr(instruction: Instruction, cpu: &mut Cpu) {
    let rm   = instruction.rm();
    let mask = instruction.msr_field_mask();

    if (instruction.0 & 0xff00) != 0xf000 {
        panic!("Invalid MSR instruction {}", instruction);
    }

    let val = cpu.reg(rm);

    cpu.msr_cpsr(val, mask);
}

fn op121_bx(instruction: Instruction, cpu: &mut Cpu) {
    let rm = instruction.rm();

    if (instruction.0 & 0xfff00) != 0xfff00 {
        // "should be one"
        panic!("Invalid BX instruction {}", instruction);
    }

    let target = cpu.reg(rm);

    // If bit 0 of the target is set we switch to Thumb mode
    let thumb = (target & 1) != 0;
    let address = target & !1;

    cpu.set_pc_thumb(address, thumb);
}

fn op140_mrs_spsr(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();

    if rd.is_pc() || (instruction.0 & 0xf0fff) != 0xf0000 {
        panic!("Invalid MSR instruction {}", instruction);
    }

    let val = cpu.spsr();

    cpu.set_reg(rd, val);
}

fn op150_cmp_lsl_i(instruction: Instruction, cpu: &mut Cpu) {
    let rn  = instruction.rn();
    let rd  = instruction.rd();
    let b   = instruction.mode1_register_lshift_imm_no_carry(cpu);

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

fn op180_orr_lsl_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let b  = instruction.mode1_register_lshift_imm_no_carry(cpu);

    let a = cpu.reg(rn);

    let val = a | b;

    cpu.set_reg(rd, val);
}

fn op181_orr_lsl_r(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let b  = instruction.mode1_register_lshift_reg_no_carry(cpu);

    let a = cpu.reg(rn);

    let val = a | b;

    cpu.set_reg(rd, val);
}

fn op19b_ldrh_pu(instruction: Instruction, cpu: &mut Cpu) {
    let rm = instruction.rm();
    let rd = instruction.rd();
    let rn = instruction.rn();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.load16(addr);

    cpu.set_reg(rd, val as u32);
}

fn op1a0_mov_lsl_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd  = instruction.rd();
    let val = instruction.mode1_register_lshift_imm_no_carry(cpu);

    cpu.set_reg(rd, val);
}

fn op1a1_mov_lsl_r(instruction: Instruction, cpu: &mut Cpu) {
    let rd  = instruction.rd();
    let val = instruction.mode1_register_lshift_reg_no_carry(cpu);

    cpu.set_reg(rd, val);
}

fn op1a2_mov_lsr_i(instruction: Instruction, cpu: &mut Cpu) {
    let dst = instruction.rd();
    let val = instruction.mode1_register_rshift_imm_no_carry(cpu);

    cpu.set_reg(dst, val);
}

fn op1a3_mov_lsr_r(instruction: Instruction, cpu: &mut Cpu) {
    let rd  = instruction.rd();
    let val = instruction.mode1_register_rshift_reg_no_carry(cpu);

    cpu.set_reg(rd, val);
}

fn op1a4_mov_asr_i(instruction: Instruction, cpu: &mut Cpu) {
    let dst = instruction.rd();
    let val = instruction.mode1_register_arshift_imm_no_carry(cpu);

    cpu.set_reg(dst, val);
}

fn op1b0_mov_lsl_is(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let (val, carry) = instruction.mode1_register_lshift_imm(cpu);

    cpu.set_reg(rd, val);

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
    cpu.set_c(carry);
}

fn op1b2_mov_lsr_is(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let (val, carry) = instruction.mode1_register_rshift_imm(cpu);

    cpu.set_reg(rd, val);

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
    cpu.set_c(carry);
}

fn op1c0_bic_lsl_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd  = instruction.rd();
    let rn  = instruction.rn();
    let b   = instruction.mode1_register_lshift_imm_no_carry(cpu);

    let a = cpu.reg(rn);

    let val = a & !b;

    cpu.set_reg(rd, val);
}

fn op1cb_strh_pui(instruction: Instruction, cpu: &mut Cpu) {
    let rn     = instruction.rn();
    let rd     = instruction.rd();
    let offset = instruction.mode3_imm_hl();

    let addr = cpu.reg(rn).wrapping_add(offset);

    let val = cpu.reg(rd);

    cpu.store16(addr, val);
}

fn op1db_ldrh_pui(instruction: Instruction, cpu: &mut Cpu) {
    let rn     = instruction.rn();
    let rd     = instruction.rd();
    let offset = instruction.mode3_imm_hl();

    let addr = cpu.reg(rn).wrapping_add(offset);

    let val = cpu.load16(addr);

    cpu.set_reg(rd, val as u32)
}

fn op1dd_ldrsb_pui(instruction: Instruction, cpu: &mut Cpu) {
    let rn     = instruction.rn();
    let rd     = instruction.rd();
    let offset = instruction.mode3_imm_hl();

    let addr = cpu.reg(rn).wrapping_add(offset);

    let val = cpu.load8(addr) as i8;

    cpu.set_reg(rd, val as u32)
}

fn op1e0_mvn_lsl_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd  = instruction.rd();
    let val = instruction.mode1_register_lshift_imm_no_carry(cpu);

    cpu.set_reg(rd, !val);
}

fn op26x_rsb_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let a  = instruction.mode1_imm_no_carry();

    let b = cpu.reg(rn);

    let val = a.wrapping_sub(b);

    cpu.set_reg(rd, val);
}

fn op27x_rsb_is(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let a  = instruction.mode1_imm_no_carry();

    let b = cpu.reg(rn);

    instruction.subs(cpu, rd, a, b);
}

fn op28x_add_i(instruction: Instruction, cpu: &mut Cpu) {
    let dst = instruction.rd();
    let rn  = instruction.rn();
    let b   = instruction.mode1_imm_no_carry();

    let a = cpu.reg(rn);

    let val = a.wrapping_add(b);

    cpu.set_reg(dst, val);
}

fn op31x_tst_i(instruction: Instruction, cpu: &mut Cpu) {
    let rn       = instruction.rn();
    let rd       = instruction.rd();
    let (imm, c) = instruction.mode1_imm(cpu);

    if rd != RegisterIndex(0) {
        // "should be zero"
        panic!("TST instruction with non-0 Rd");
    }

    let val = cpu.reg(rn) & imm;

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
    cpu.set_c(c);
}

fn op35x_cmp_i(instruction: Instruction, cpu: &mut Cpu) {
    let rn  = instruction.rn();
    let rd  = instruction.rd();
    let b   = instruction.mode1_imm_no_carry();

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

fn op38x_orr_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let b  = instruction.mode1_imm_no_carry();

    let a = cpu.reg(rn);

    let val = a | b;

    cpu.set_reg(rd, val);
}

fn op3ax_mov_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd  = instruction.rd();
    let rn  = instruction.rn();
    let val = instruction.mode1_imm_no_carry();

    if rn != RegisterIndex(0) {
        // "should be zero"
        panic!("MOV instruction with non-0 Rn");
    }

    cpu.set_reg(rd, val);
}

fn op3cx_bic_i(instruction: Instruction, cpu: &mut Cpu) {
    let rd = instruction.rd();
    let rn = instruction.rn();
    let b  = instruction.mode1_imm_no_carry();

    let a = cpu.reg(rn);

    let val = a & !b;

    cpu.set_reg(rd, val);
}

fn op3ex_mvn_i(instruction: Instruction, cpu: &mut Cpu) {
    let dst = instruction.rd();
    let rn = instruction.rn();
    let val = instruction.mode1_imm_no_carry();

    if rn != RegisterIndex(0) {
        // "should be zero"
        panic!("MVN instruction with non-0 Rn");
    }

    cpu.set_reg(dst, !val);
}

fn op48x_str_u(instruction: Instruction, cpu: &mut Cpu) {
    let src    = instruction.rd();
    let base   = instruction.rn();
    let offset = instruction.mode2_offset_imm();

    if src.is_pc() {
        // Implementation defined
        panic!("PC stored in STR");
    }

    if base.is_pc() {
        // Unpredictable
        panic!("PC post-indexed");
    }

    let addr = cpu.reg(base);

    let val = cpu.reg(src);

    cpu.store32(addr, val);

    let post_addr = addr.wrapping_add(offset);

    cpu.set_reg(base, post_addr)
}

fn op58x_str_pu(instruction: Instruction, cpu: &mut Cpu) {
    let src    = instruction.rd();
    let base   = instruction.rn();
    let offset = instruction.mode2_offset_imm();

    if src.is_pc() {
        // Implementation defined
        panic!("PC stored in STR");
    }

    let addr = cpu.reg(base).wrapping_add(offset);

    let val = cpu.reg(src);

    cpu.store32(addr, val);
}

fn op49x_ldr_u(instruction: Instruction, cpu: &mut Cpu) {
    let rd     = instruction.rd();
    let rn     = instruction.rn();
    let offset = instruction.mode2_offset_imm();

    if rn.is_pc() {
        panic!("unpredictable LDR");
    }

    let addr = cpu.reg(rn);

    let post_addr = addr.wrapping_add(offset);

    let val = instruction.ldr(cpu, addr);

    cpu.set_reg(rn, post_addr);
    cpu.set_reg_pc_mask(rd, val);
}

fn op59x_ldr_pu(instruction: Instruction, cpu: &mut Cpu) {
    let dst    = instruction.rd();
    let base   = instruction.rn();
    let offset = instruction.mode2_offset_imm();

    let addr = cpu.reg(base).wrapping_add(offset);

    let val = instruction.ldr(cpu, addr);

    cpu.set_reg_pc_mask(dst, val);
}

fn op5cx_strb_pu(instruction: Instruction, cpu: &mut Cpu) {
    let src    = instruction.rd();
    let base   = instruction.rn();
    let offset = instruction.mode2_offset_imm();

    if src.is_pc() {
        // Unpredictable (not "implementation defined" like STR
        // for some reason)
        panic!("PC stored in STRB");
    }

    let addr = cpu.reg(base).wrapping_add(offset);

    let val = cpu.reg(src);

    cpu.store8(addr, val);
}

fn op5dx_ldrb_pu(instruction: Instruction, cpu: &mut Cpu) {
    let dst    = instruction.rd();
    let base   = instruction.rn();
    let offset = instruction.mode2_offset_imm();

    let addr = cpu.reg(base).wrapping_add(offset);

    let val = cpu.load8(addr);

    cpu.set_reg_pc_mask(dst, val as u32);
}

fn op780_str_ipu(instruction: Instruction, cpu: &mut Cpu) {
    let src    = instruction.rd();
    let base   = instruction.rn();
    let offset = instruction.mode2_register_lshift(cpu);

    if src.is_pc() {
        // Implementation defined
        panic!("PC stored in STR");
    }

    let addr = cpu.reg(base).wrapping_add(offset);

    let val = cpu.reg(src);

    cpu.store32(addr, val);
}

fn op790_ldr_ipu(instruction: Instruction, cpu: &mut Cpu) {
    let dst    = instruction.rd();
    let base   = instruction.rn();
    let offset = instruction.mode2_register_lshift(cpu);

    let addr = cpu.reg(base).wrapping_add(offset);

    let val = instruction.ldr(cpu, addr);

    cpu.set_reg_pc_mask(dst, val);
}

fn op88x_stm_u(instruction: Instruction, cpu: &mut Cpu) {
    let rn = instruction.rn();

    if rn.is_pc() {
        panic!("PC-relative STM!");
    }

    let start_addr = cpu.reg(rn);

    instruction.stm(cpu, start_addr);
}

fn op89x_ldm_u(instruction: Instruction, cpu: &mut Cpu) {
    let rn   = instruction.rn();
    let list = instruction.register_list();

    if rn.is_pc()  {
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
}

fn op8ax_stm_uw(instruction: Instruction, cpu: &mut Cpu) {
    let rn = instruction.rn();

    if rn.is_pc() {
        panic!("PC-relative STM!");
    }

    let start_addr = cpu.reg(rn);

    let end_addr = instruction.stm(cpu, start_addr);

    cpu.set_reg(rn, end_addr);
}

fn op8bx_ldm_uw(instruction: Instruction, cpu: &mut Cpu) {
    let rn   = instruction.rn();
    let list = instruction.register_list();

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

fn op8fx_ldm_spsr_uw(instruction: Instruction, cpu: &mut Cpu) {
    let rn   = instruction.rn();
    let list = instruction.register_list();

    if rn.is_pc() || (list & (1 << rn.0)) != 0 {
        // Can't load to the base register if we want writeback
        panic!("Unpredictable LDM");
    }

    if (list & (1 << 15)) == 0 {
        panic!("LDM SPSR without PC!");
    }

    let mut addr = cpu.reg(rn);

    for i in 0..15 {
        if ((list >> i) & 1) != 0 {
            let reg = RegisterIndex(i);

            let val = cpu.load32(addr);

            cpu.set_reg(reg, val);

            addr = addr.wrapping_add(4);
        }
    }

    let pc = cpu.load32(addr);
    addr = addr.wrapping_add(4);

    cpu.set_reg(rn, addr);

    let spsr = cpu.spsr();

    cpu.set_pc_cpsr(pc, spsr);
}

fn op92x_stm_pw(instruction: Instruction, cpu: &mut Cpu) {
    let rn   = instruction.rn();
    let list = instruction.register_list();

    if rn.is_pc() {
        // Using PC as base if we want writeback is unpredictable
        panic!("PC-relative STM!");
    }

    let num_regs = list.count_ones();

    let start_addr = cpu.reg(rn).wrapping_sub(4 * num_regs);

    instruction.stm(cpu, start_addr);

    cpu.set_reg(rn, start_addr);
}

fn opaxx_b(instruction: Instruction, cpu: &mut Cpu) {
    let offset = instruction.branch_imm_offset();

    let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

    cpu.set_pc(pc);
}

fn opbxx_bl(instruction: Instruction, cpu: &mut Cpu) {
    let offset = instruction.branch_imm_offset();

    let pc = cpu.registers[15].wrapping_add(offset);

    let ra = cpu.next_pc;

    cpu.set_reg(RegisterIndex(14), ra);

    cpu.set_pc(pc);
}

fn opfxx_swi(_: Instruction, cpu: &mut Cpu) {
    cpu.swi();
}

static OPCODE_LUT: [fn (Instruction, &mut Cpu); 4096] = [
    // 0x000
    and::<Mode1LslImm>, unimplemented, and::<Mode1LsrImm>, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    and::<Mode1LslImm>, mul, and::<Mode1LsrImm>, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x010
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x020
    eor::<Mode1LslImm>, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    eor::<Mode1LslImm>, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x030
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x040
    sub::<Mode1LslImm>, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    sub::<Mode1LslImm>, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x050
    subs::<Mode1LslImm>, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    subs::<Mode1LslImm>, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x060
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x070
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x080
    op080_add_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op080_add_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x090
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x0a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x0b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x0c0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x0d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x0e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x0f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x100
    op100_mrs_cpsr, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x110
    op110_tst_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op110_tst_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x120
    op120_msr_cpsr, op121_bx, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x130
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x140
    op140_mrs_spsr, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x150
    op150_cmp_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op150_cmp_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x160
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x170
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x180
    op180_orr_lsl_i, op181_orr_lsl_r, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op180_orr_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x190
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, op19b_ldrh_pu,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x1a0
    op1a0_mov_lsl_i, op1a1_mov_lsl_r, op1a2_mov_lsr_i, op1a3_mov_lsr_r,
    op1a4_mov_asr_i, unimplemented, unimplemented, unimplemented,
    op1a0_mov_lsl_i, unimplemented, op1a2_mov_lsr_i, unimplemented,
    op1a4_mov_asr_i, unimplemented, unimplemented, unimplemented,

    // 0x1b0
    op1b0_mov_lsl_is, unimplemented, op1b2_mov_lsr_is, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op1b0_mov_lsl_is, unimplemented, op1b2_mov_lsr_is, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x1c0
    op1c0_bic_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op1c0_bic_lsl_i, unimplemented, unimplemented, op1cb_strh_pui,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x1d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, op1db_ldrh_pui,
    unimplemented, op1dd_ldrsb_pui, unimplemented, unimplemented,

    // 0x1e0
    op1e0_mvn_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op1e0_mvn_lsl_i, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x1f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x200
    and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>,
    and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>,
    and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>,
    and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>, and::<Mode1Imm>,

    // 0x210
    ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>,
    ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>,
    ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>,
    ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>, ands::<Mode1Imm>,

    // 0x220
    eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>,
    eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>,
    eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>,
    eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>, eor::<Mode1Imm>,

    // 0x230
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x240
    sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>,
    sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>,
    sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>,
    sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>, sub::<Mode1Imm>,

    // 0x250
    subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>,
    subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>,
    subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>,
    subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>, subs::<Mode1Imm>,

    // 0x260
    op26x_rsb_i, op26x_rsb_i, op26x_rsb_i, op26x_rsb_i,
    op26x_rsb_i, op26x_rsb_i, op26x_rsb_i, op26x_rsb_i,
    op26x_rsb_i, op26x_rsb_i, op26x_rsb_i, op26x_rsb_i,
    op26x_rsb_i, op26x_rsb_i, op26x_rsb_i, op26x_rsb_i,

    // 0x270
    op27x_rsb_is, op27x_rsb_is, op27x_rsb_is, op27x_rsb_is,
    op27x_rsb_is, op27x_rsb_is, op27x_rsb_is, op27x_rsb_is,
    op27x_rsb_is, op27x_rsb_is, op27x_rsb_is, op27x_rsb_is,
    op27x_rsb_is, op27x_rsb_is, op27x_rsb_is, op27x_rsb_is,

    // 0x280
    op28x_add_i, op28x_add_i, op28x_add_i, op28x_add_i,
    op28x_add_i, op28x_add_i, op28x_add_i, op28x_add_i,
    op28x_add_i, op28x_add_i, op28x_add_i, op28x_add_i,
    op28x_add_i, op28x_add_i, op28x_add_i, op28x_add_i,

    // 0x290
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2c0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x300
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x310
    op31x_tst_i, op31x_tst_i, op31x_tst_i, op31x_tst_i,
    op31x_tst_i, op31x_tst_i, op31x_tst_i, op31x_tst_i,
    op31x_tst_i, op31x_tst_i, op31x_tst_i, op31x_tst_i,
    op31x_tst_i, op31x_tst_i, op31x_tst_i, op31x_tst_i,

    // 0x320
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x330
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x340
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x350
    op35x_cmp_i, op35x_cmp_i, op35x_cmp_i, op35x_cmp_i,
    op35x_cmp_i, op35x_cmp_i, op35x_cmp_i, op35x_cmp_i,
    op35x_cmp_i, op35x_cmp_i, op35x_cmp_i, op35x_cmp_i,
    op35x_cmp_i, op35x_cmp_i, op35x_cmp_i, op35x_cmp_i,

    // 0x360
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x370
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x380
    op38x_orr_i, op38x_orr_i, op38x_orr_i, op38x_orr_i,
    op38x_orr_i, op38x_orr_i, op38x_orr_i, op38x_orr_i,
    op38x_orr_i, op38x_orr_i, op38x_orr_i, op38x_orr_i,
    op38x_orr_i, op38x_orr_i, op38x_orr_i, op38x_orr_i,

    // 0x390
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x3a0
    op3ax_mov_i, op3ax_mov_i, op3ax_mov_i, op3ax_mov_i,
    op3ax_mov_i, op3ax_mov_i, op3ax_mov_i, op3ax_mov_i,
    op3ax_mov_i, op3ax_mov_i, op3ax_mov_i, op3ax_mov_i,
    op3ax_mov_i, op3ax_mov_i, op3ax_mov_i, op3ax_mov_i,

    // 0x3b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x3c0
    op3cx_bic_i, op3cx_bic_i, op3cx_bic_i, op3cx_bic_i,
    op3cx_bic_i, op3cx_bic_i, op3cx_bic_i, op3cx_bic_i,
    op3cx_bic_i, op3cx_bic_i, op3cx_bic_i, op3cx_bic_i,
    op3cx_bic_i, op3cx_bic_i, op3cx_bic_i, op3cx_bic_i,

    // 0x3d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x3e0
    op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i,
    op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i,
    op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i,
    op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i, op3ex_mvn_i,

    // 0x3f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x400
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x410
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x420
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x430
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x440
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x450
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x460
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x470
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x480
    op48x_str_u, op48x_str_u, op48x_str_u, op48x_str_u,
    op48x_str_u, op48x_str_u, op48x_str_u, op48x_str_u,
    op48x_str_u, op48x_str_u, op48x_str_u, op48x_str_u,
    op48x_str_u, op48x_str_u, op48x_str_u, op48x_str_u,

    // 0x490
    op49x_ldr_u, op48x_str_u, op48x_str_u, op48x_str_u,
    op48x_str_u, op48x_str_u, op48x_str_u, op48x_str_u,
    op48x_str_u, op48x_str_u, op48x_str_u, op48x_str_u,
    op48x_str_u, op48x_str_u, op48x_str_u, op48x_str_u,

    // 0x4a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x4b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x4c0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x4d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x4e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x4f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x500
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x510
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x520
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x530
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x540
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x550
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x560
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x570
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x580
    op58x_str_pu, op58x_str_pu, op58x_str_pu, op58x_str_pu,
    op58x_str_pu, op58x_str_pu, op58x_str_pu, op58x_str_pu,
    op58x_str_pu, op58x_str_pu, op58x_str_pu, op58x_str_pu,
    op58x_str_pu, op58x_str_pu, op58x_str_pu, op58x_str_pu,

    // 0x590
    op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu,
    op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu,
    op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu,
    op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu, op59x_ldr_pu,

    // 0x5a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x5b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x5c0
    op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu,
    op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu,
    op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu,
    op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu, op5cx_strb_pu,

    // 0x5d0
    op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu,
    op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu,
    op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu,
    op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu, op5dx_ldrb_pu,

    // 0x5e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x5f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x600
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x610
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x620
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x630
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x640
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x650
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x660
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x670
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x680
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x690
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x6a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x6b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x6c0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x6d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x6e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x6f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x700
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x710
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x720
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x730
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x740
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x750
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x760
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x770
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x780
    op780_str_ipu, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op780_str_ipu, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x790
    op790_ldr_ipu, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op790_ldr_ipu, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x7a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x7b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x7c0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x7d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x7e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x7f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x800
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x810
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x820
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x830
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x840
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x850
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x860
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x870
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x880
    op88x_stm_u, op88x_stm_u, op88x_stm_u, op88x_stm_u,
    op88x_stm_u, op88x_stm_u, op88x_stm_u, op88x_stm_u,
    op88x_stm_u, op88x_stm_u, op88x_stm_u, op88x_stm_u,
    op88x_stm_u, op88x_stm_u, op88x_stm_u, op88x_stm_u,

    // 0x890
    op89x_ldm_u, op89x_ldm_u, op89x_ldm_u, op89x_ldm_u,
    op89x_ldm_u, op89x_ldm_u, op89x_ldm_u, op89x_ldm_u,
    op89x_ldm_u, op89x_ldm_u, op89x_ldm_u, op89x_ldm_u,
    op89x_ldm_u, op89x_ldm_u, op89x_ldm_u, op89x_ldm_u,

    // 0x8a0
    op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw,
    op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw,
    op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw,
    op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw, op8ax_stm_uw,

    // 0x8b0
    op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw,
    op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw,
    op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw,
    op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw, op8bx_ldm_uw,

    // 0x8c0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x8d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x8e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x8f0
    op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw,
    op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw,
    op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw,
    op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw, op8fx_ldm_spsr_uw,

    // 0x900
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x910
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x920
    op92x_stm_pw, op92x_stm_pw, op92x_stm_pw, op92x_stm_pw,
    op92x_stm_pw, op92x_stm_pw, op92x_stm_pw, op92x_stm_pw,
    op92x_stm_pw, op92x_stm_pw, op92x_stm_pw, op92x_stm_pw,
    op92x_stm_pw, op92x_stm_pw, op92x_stm_pw, op92x_stm_pw,

    // 0x930
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x940
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x950
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x960
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x970
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x980
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x990
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x9a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x9b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x9c0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x9d0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x9e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x9f0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xa00
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa10
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa20
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa30
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa40
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa50
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa60
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa70
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa80
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xa90
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xaa0
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xab0
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xac0
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xad0
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xae0
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xaf0
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,
    opaxx_b, opaxx_b, opaxx_b, opaxx_b,

    // 0xb00
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb10
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb20
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb30
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb40
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb50
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb60
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb70
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb80
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xb90
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xba0
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xbb0
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xbc0
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xbd0
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xbe0
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xbf0
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,
    opbxx_bl, opbxx_bl, opbxx_bl, opbxx_bl,

    // 0xc00
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc10
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc20
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc30
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc40
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc50
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc60
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc70
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc80
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xc90
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xca0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xcb0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xcc0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xcd0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xce0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xcf0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd00
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd10
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd20
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd30
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd40
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd50
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd60
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd70
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd80
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xd90
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xda0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xdb0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xdc0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xdd0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xde0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xdf0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe00
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe10
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe20
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe30
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe40
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe50
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe60
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe70
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe80
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xe90
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xea0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xeb0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xec0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xed0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xee0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xef0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0xf00
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf10
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf20
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf30
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf40
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf50
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf60
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf70
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf80
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xf90
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xfa0
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xfb0
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xfc0
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xfd0
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xfe0
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,

    // 0xff0
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
    opfxx_swi, opfxx_swi, opfxx_swi, opfxx_swi,
];
