//! THUMBv1 instruction set

use std::fmt;

use memory::{Word, HalfWord, Byte};
use debugger::Debugger;

use super::{Cpu, RegisterIndex};

pub fn execute<D>(cpu: &mut Cpu, debugger: &mut D, instruction: u16)
    where D: Debugger {
    let instruction = Instruction(instruction);

    instruction.execute(debugger, cpu);
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

    fn reg_6(self) -> RegisterIndex {
        let r = (self.0 >> 6) & 7;

        RegisterIndex(r as u32)
    }

    fn reg_8(self) -> RegisterIndex {
        let r = (self.0 >> 8) & 7;

        RegisterIndex(r as u32)
    }

    fn reg_0_full(self) -> RegisterIndex {
        let lo = (self.0 & 0x7) as u32;
        let hi = ((self.0 >> 7) & 1) as u32;

        RegisterIndex((hi << 3) | lo)
    }

    fn reg_3_full(self) -> RegisterIndex {
        let r = (self.0 >> 3) & 0xf;

        RegisterIndex(r as u32)
    }

    fn imm8(self) -> u32 {
        (self.0 & 0xff) as u32
    }

    fn imm7(self) -> u32 {
        (self.0 & 0x7f) as u32
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

    fn adds(self, cpu: &mut Cpu, a: u32, b: u32) -> u32 {
        let val = a.wrapping_add(b);

        let a_neg = (a as i32) < 0;
        let b_neg = (b as i32) < 0;
        let v_neg = (val as i32) < 0;

        cpu.set_n(v_neg);
        cpu.set_z(val == 0);
        cpu.set_c(val < a);
        cpu.set_v((a_neg == b_neg) & (a_neg ^ v_neg));

        val
    }

    fn subs(self, cpu: &mut Cpu, a: u32, b: u32) -> u32 {
        let val = a.wrapping_sub(b);

        let a_neg = (a as i32) < 0;
        let b_neg = (b as i32) < 0;
        let v_neg = (val as i32) < 0;

        cpu.set_n(v_neg);
        cpu.set_z(val == 0);
        cpu.set_c(a >= b);
        cpu.set_v((a_neg ^ b_neg) & (a_neg ^ v_neg));

        val
    }

    fn execute<D>(self, debugger: &mut D, cpu: &mut Cpu)
        where D: Debugger {
        let handler = OPCODE_LUT[self.opcode() as usize];

        handler(self, debugger, cpu);
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

fn unimplemented(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    panic!("Unimplemented instruction {} ({:03x})\n{:?}",
           instruction,
           instruction.opcode(),
           cpu);
}

fn op00x_lsl_ri5(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rm     = instruction.reg_3();
    let shift  = instruction.imm5();

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

fn op02x_lsr_ri5(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rm     = instruction.reg_3();
    let shift  = instruction.imm5();

    let val = cpu.reg(rm);

    let (val, carry) =
        match shift {
            0 => {
                // 0 is a special case to shift by 32 places
                let carry = (val & (1 << 31)) != 0;

                (0, carry)
            }
            _ => {
                let carry = (val & (1 << (shift - 1))) != 0;

                (val >> shift, carry)
            }
        };

    cpu.set_reg(rd, val);
    cpu.set_n(false);
    cpu.set_z(val == 0);
    cpu.set_c(carry);
}

fn op04x_asr_ri5(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rm     = instruction.reg_3();
    let shift  = instruction.imm5();

    let val = cpu.reg(rm);

    let ival = val as i32;

    let (ival, carry) =
        match shift {
            0 => {
                // 0 is a special case to shift by 32 places
                let carry = ival < 0;

                (ival >> 31, carry)
            }
            _ => {
                let carry = (val & (1 << (shift - 1))) != 0;

                (ival >> shift, carry)
            }
        };

    cpu.set_reg(rd, ival as u32);
    cpu.set_n(ival < 0);
    cpu.set_z(ival == 0);
    cpu.set_c(carry);
}

fn op06x_add_rr(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let a = cpu.reg(rn);
    let b = cpu.reg(rm);

    let val = instruction.adds(cpu, a, b);

    cpu.set_reg(rd, val);
}

fn op06x_sub_rr(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let a = cpu.reg(rn);
    let b = cpu.reg(rm);

    let val = instruction.subs(cpu, a, b);

    cpu.set_reg(rd, val);
}

fn op07x_add_i3(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let b  = instruction.imm3();

    let a = cpu.reg(rn);

    let val = instruction.adds(cpu, a, b);

    cpu.set_reg(rd, val);
}

fn op07x_sub_i3(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let b  = instruction.imm3();

    let a = cpu.reg(rn);

    let val = instruction.subs(cpu, a, b);

    cpu.set_reg(rd, val);
}

fn op08x_mov_i8(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd  = instruction.reg_8();
    let val = instruction.imm8();

    cpu.set_reg(rd, val);

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op0ax_cmp_i8(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rn  = instruction.reg_8();
    let b   = instruction.imm8();

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

fn op0cx_add_i8(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd  = instruction.reg_8();
    let b   = instruction.imm8();

    let a = cpu.reg(rd);

    let val = instruction.adds(cpu, a, b);

    cpu.set_reg(rd, val);
}

fn op0ex_sub_i8(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd  = instruction.reg_8();
    let b   = instruction.imm8();

    let a = cpu.reg(rd);

    let val = instruction.subs(cpu, a, b);

    cpu.set_reg(rd, val);
}

fn op100_and(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rd);
    let b = cpu.reg(rm);

    let val = a & b;

    cpu.set_reg(rd, val);
    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op101_eor(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rd);
    let b = cpu.reg(rm);

    let val = a ^ b;

    cpu.set_reg(rd, val);
    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op102_lsl_r(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rs = instruction.reg_3();

    let shift = cpu.reg(rs) & 0xff;

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

fn op103_lsr_r(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rs = instruction.reg_3();

    let shift = cpu.reg(rs) & 0xff;

    let val = cpu.reg(rd);

    let val =
        match shift {
            0 => val,
            1...31 => {
                let carry = (val & (1 << (shift - 1))) != 0;

                cpu.set_c(carry);

                val >> shift
            }
            32 => {
                cpu.set_c((val as i32) < 0);

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

fn op104_asr_r(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rs = instruction.reg_3();

    let shift = cpu.reg(rs) & 0xff;
    let val = cpu.reg(rd);

    let val =
        match shift {
            0 => val,
            1...31 => {
                let carry = (val >> (shift - 1)) & 1 != 0;

                cpu.set_c(carry);
                ((val as i32) >> shift) as u32
            }
            _ => {
                let carry = (val >> 31) & 1 != 0;

                cpu.set_c(carry);
                ((val as i32) >> 31) as u32
            }
        };

    cpu.set_reg(rd, val);
    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op105_adc_rr(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rd);
    let b = cpu.reg(rm);

    // Add with carry
    let val = a.wrapping_add(b).wrapping_add(cpu.c() as u32);

    let a_neg = (a as i32) < 0;
    let b_neg = (b as i32) < 0;
    let v_neg = (val as i32) < 0;

    cpu.set_reg(rd, val);

    cpu.set_n(v_neg);
    cpu.set_z(val == 0);
    cpu.set_c(val < a);
    cpu.set_v((a_neg == b_neg) & (a_neg ^ v_neg));
}

fn op107_ror(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rs = instruction.reg_3();

    let rot = cpu.reg(rs);
    let val = cpu.reg(rd);

    let val =
        if (rot & 0xff) == 0 {
            val
        } else if (rot & 0x1f) == 0 {
            let carry = (val >> 31) & 1 != 0;

            cpu.set_c(carry);
            val
        } else {
            let rot = rot & 0x1f;

            let carry = (val >> (rot - 1)) & 1 != 0;

            cpu.set_c(carry);
            val.rotate_right(rot)
        };

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op108_tst(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rn = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rn);
    let b = cpu.reg(rm);

    let val = a & b;

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op109_neg(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let b = cpu.reg(rm);

    let val = instruction.subs(cpu, 0, b);

    cpu.set_reg(rd, val);
}

fn op10a_cmp(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rn = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rn);
    let b = cpu.reg(rm);

    instruction.subs(cpu, a, b);
}

fn op10b_cmn(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rn = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rn);
    let b = cpu.reg(rm);

    instruction.adds(cpu, a, b);
}

fn op10c_orr(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rd);
    let b = cpu.reg(rm);

    let val = a | b;

    cpu.set_reg(rd, val);
    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op10d_mul(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let a = cpu.reg(rd);
    let b = cpu.reg(rm);

    let val = a.wrapping_mul(b);

    cpu.set_reg(rd, val);
    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op10e_bic(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let val = cpu.reg(rd) & !cpu.reg(rm);

    cpu.set_reg(rd, val);

    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op10f_mvn(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rm = instruction.reg_3();

    let val = !cpu.reg(rm);

    cpu.set_reg(rd, val);
    cpu.set_n((val as i32) < 0);
    cpu.set_z(val == 0);
}

fn op111_add_hi(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rm = instruction.reg_3_full();
    let rd = instruction.reg_0_full();

    let a = cpu.reg(rd);
    let b = cpu.reg(rm);

    let val = a.wrapping_add(b);

    cpu.set_reg(rd, val);
}

fn op115_cmp_hi(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rn = instruction.reg_0_full();
    let rm = instruction.reg_3_full();

    let a = cpu.reg(rn);
    let b = cpu.reg(rm);

    instruction.subs(cpu, a, b);
}

fn op11c_bx(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rm = instruction.reg_3_full();

    if (instruction.0 & 7) != 0 {
        // Should be 0
        panic!("Invalid BX instruction {}", instruction);
    }

    let target = cpu.reg(rm);

    let thumb = (target & 1) != 0;

    cpu.set_pc_thumb(target & !1, thumb);
}

/// Also known as MOV(3)
fn op118_cpy(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rm = instruction.reg_3_full();
    let rd = instruction.reg_0_full();

    let val = cpu.reg(rm);


    let val =
        if rd.is_pc() {
            val & !1
        } else {
            val
        };

    cpu.set_reg(rd, val);
}

fn op12x_ldr_pc(instruction: Instruction,
                debugger: &mut Debugger,
                cpu: &mut Cpu) {
    let rd = instruction.reg_8();
    let offset = instruction.imm8() << 2;

    let base = cpu.reg(RegisterIndex(15)) & !3;

    let addr = base.wrapping_add(offset);

    let val = cpu.load::<Word>(debugger, addr);

    cpu.set_reg(rd, val);
}

fn op14x_str_rr(instruction: Instruction,
                debugger: &mut Debugger,
                cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.reg(rd);

    cpu.store::<Word>(debugger, addr, val);
}

fn op14x_strh_rr(instruction: Instruction,
                 debugger: &mut Debugger,
                 cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    if (addr & 1) != 0 {
        panic!("Unpredictable STRH");
    }

    let val = cpu.reg(rd);

    cpu.store::<HalfWord>(debugger, addr, val);
}

fn op15x_strb_rr(instruction: Instruction,
                 debugger: &mut Debugger,
                 cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.reg(rd);

    cpu.store::<Byte>(debugger, addr, val);
}

fn op15x_ldrsb_rr(instruction: Instruction,
                  debugger: &mut Debugger,
                  cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.load::<Byte>(debugger, addr) as i8;

    cpu.set_reg(rd, val as u32);
}

fn op16x_ldr_rr(instruction: Instruction,
                debugger: &mut Debugger,
                cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.load::<Word>(debugger, addr);

    cpu.set_reg(rd, val);
}

fn op16x_ldrh_rr(instruction: Instruction,
                 debugger: &mut Debugger,
                 cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.load::<HalfWord>(debugger, addr);

    cpu.set_reg(rd, val as u32);
}

fn op17x_ldrb_rr(instruction: Instruction,
                 debugger: &mut Debugger,
                 cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.load::<Byte>(debugger, addr);

    cpu.set_reg(rd, val as u32);
}

fn op17x_ldrsh_rr(instruction: Instruction,
                  debugger: &mut Debugger,
                  cpu: &mut Cpu) {
    let rd = instruction.reg_0();
    let rn = instruction.reg_3();
    let rm = instruction.reg_6();

    let addr = cpu.reg(rn).wrapping_add(cpu.reg(rm));

    let val = cpu.load::<HalfWord>(debugger, addr) as i16;

    cpu.set_reg(rd, val as u32);
}

fn op18x_str_ri5(instruction: Instruction,
                 debugger: &mut Debugger,
                 cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rn     = instruction.reg_3();
    let offset = instruction.imm5() << 2;

    let base = cpu.reg(rn);

    let addr = base.wrapping_add(offset);

    let val = cpu.reg(rd);

    cpu.store::<Word>(debugger, addr, val);
}

fn op1ax_ldr_ri5(instruction: Instruction,
                 debugger: &mut Debugger,
                 cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rn     = instruction.reg_3();
    let offset = instruction.imm5() << 2;

    let base = cpu.reg(rn);

    let addr = base.wrapping_add(offset);

    let val = cpu.load::<Word>(debugger, addr);

    cpu.set_reg(rd, val);
}

fn op1cx_strb_ri5(instruction: Instruction,
                  debugger: &mut Debugger,
                  cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rn     = instruction.reg_3();
    let offset = instruction.imm5();

    let addr = cpu.reg(rn).wrapping_add(offset);

    let val = cpu.reg(rd);

    cpu.store::<Byte>(debugger, addr, val);
}

fn op1ex_ldrb_ri5(instruction: Instruction,
                  debugger: &mut Debugger,
                  cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rn     = instruction.reg_3();
    let offset = instruction.imm5();

    let addr = cpu.reg(rn).wrapping_add(offset);

    let val = cpu.load::<Byte>(debugger, addr);

    cpu.set_reg(rd, val as u32);
}

fn op20x_strh_ri5(instruction: Instruction,
                  debugger: &mut Debugger,
                  cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rn     = instruction.reg_3();
    let offset = instruction.imm5() << 1;

    let addr = cpu.reg(rn).wrapping_add(offset);

    if (addr & 1) != 0 {
        panic!("Unpredictable STRH");
    }

    let val = cpu.reg(rd);

    cpu.store::<HalfWord>(debugger, addr, val);
}

fn op22x_ldrh_ri5(instruction: Instruction,
                  debugger: &mut Debugger,
                  cpu: &mut Cpu) {
    let rd     = instruction.reg_0();
    let rn     = instruction.reg_3();
    let offset = instruction.imm5() << 1;

    let addr = cpu.reg(rn).wrapping_add(offset);

    let val = cpu.load::<HalfWord>(debugger, addr);

    cpu.set_reg(rd, val as u32);
}

fn op24x_str_sp(instruction: Instruction,
                debugger: &mut Debugger,
                cpu: &mut Cpu) {
    let rd  = instruction.reg_8();
    let imm = instruction.imm8() << 2;

    let sp = RegisterIndex(13);

    let addr = cpu.reg(sp).wrapping_add(imm);

    let val = cpu.reg(rd);

    cpu.store::<Word>(debugger, addr, val);
}

fn op26x_ldr_sp(instruction: Instruction,
                debugger: &mut Debugger,
                cpu: &mut Cpu) {
    let rd  = instruction.reg_8();
    let imm = instruction.imm8() << 2;

    let sp = RegisterIndex(13);

    let addr = cpu.reg(sp).wrapping_add(imm);

    let val = cpu.load::<Word>(debugger, addr);

    cpu.set_reg(rd, val);
}

fn op28x_add_pc(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd  = instruction.reg_8();
    let offset = instruction.imm8() << 2;

    let pc = RegisterIndex(15);

    let val = cpu.reg(pc).wrapping_add(offset);

    cpu.set_reg(rd, val & !3);
}

fn op2ax_add_sp_i(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let rd     = instruction.reg_8();
    let offset = instruction.imm8() << 2;

    let sp = RegisterIndex(13);

    let val = cpu.reg(sp);

    cpu.set_reg(rd, val.wrapping_add(offset));
}

fn op2c0_add_sp(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.imm7() << 2;

    let sp = RegisterIndex(13);

    let val = cpu.reg(sp);

    cpu.set_reg(sp, val.wrapping_add(offset));
}

fn op2c2_sub_sp(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.imm7() << 2;

    let sp = RegisterIndex(13);

    let val = cpu.reg(sp);

    cpu.set_reg(sp, val.wrapping_sub(offset));
}

fn op2d0_push(instruction: Instruction,
              debugger: &mut Debugger,
              cpu: &mut Cpu) {
    let list = instruction.register_list();

    // Push are SP-relative
    let sp = RegisterIndex(13);

    let num_regs = list.count_ones();

    if num_regs == 0 {
        panic!("Unpredictable PUSH {}", instruction);
    }

    let start_addr = cpu.reg(sp).wrapping_sub(4 * num_regs);

    let mut addr = start_addr;

    for i in 0..8 {
        if ((list >> i) & 1) != 0 {
            let reg = RegisterIndex(i);

            let val = cpu.reg(reg);
            cpu.store::<Word>(debugger, addr, val);

            addr = addr.wrapping_add(4);
        }
    }

    cpu.set_reg(sp, start_addr);
}

fn op2d4_push_lr(instruction: Instruction,
                 debugger: &mut Debugger,
                 cpu: &mut Cpu) {
    let list = instruction.register_list();

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
            cpu.store::<Word>(debugger, addr, val);

            addr = addr.wrapping_add(4);
        }
    }

    // Push LR
    let lr = cpu.reg(RegisterIndex(14));
    cpu.store::<Word>(debugger, addr, lr);

    cpu.set_reg(sp, start_addr);
}

fn op2f0_pop(instruction: Instruction,
             debugger: &mut Debugger,
             cpu: &mut Cpu) {
    let list = instruction.register_list();

    // Pop are SP-relative
    let sp = RegisterIndex(13);

    let num_regs = list.count_ones();

    if num_regs == 0 {
        panic!("Unpredictable PUSH {}", instruction);
    }

    let mut addr = cpu.reg(sp);

    for i in 0..8 {
        if ((list >> i) & 1) != 0 {
            let reg = RegisterIndex(i);

            let val = cpu.load::<Word>(debugger, addr);

            cpu.set_reg(reg, val);

            addr = addr.wrapping_add(4);
        }
    }

    cpu.set_reg(sp, addr);
}

fn op2f4_pop_pc(instruction: Instruction,
                debugger: &mut Debugger,
                cpu: &mut Cpu) {
    let list = instruction.register_list();

    // Pop are SP-relative
    let sp = RegisterIndex(13);

    let mut addr = cpu.reg(sp);

    for i in 0..8 {
        if ((list >> i) & 1) != 0 {
            let reg = RegisterIndex(i);

            let val = cpu.load::<Word>(debugger, addr);

            cpu.set_reg(reg, val);

            addr = addr.wrapping_add(4);
        }
    }

    // Load PC
    let pc = cpu.load::<Word>(debugger, addr);
    cpu.set_pc(pc & !1);
    addr = addr.wrapping_add(4);

    cpu.set_reg(sp, addr);
}

fn op30x_stmia(instruction: Instruction,
               debugger: &mut Debugger,
               cpu: &mut Cpu) {
    let list = instruction.register_list();
    let rn   = instruction.reg_8();

    let mut addr = cpu.reg(rn);

    let mut first = true;

    for i in 0..8 {
        if ((list >> i) & 1) != 0 {
            let reg = RegisterIndex(i);

            // If Rn is specified in the register_list and it's the
            // first entry then the original value is stored,
            // otherwise it's "unpredictable".
            if !first && reg == rn {
                panic!("Unpredictable STM! {}", instruction);
            }

            let val = cpu.reg(reg);
            cpu.store::<Word>(debugger, addr, val);

            addr = addr.wrapping_add(4);
            first = false;
        }
    }

    cpu.set_reg(rn, addr);
}

fn op32x_ldmia(instruction: Instruction,
               debugger: &mut Debugger,
               cpu: &mut Cpu) {
    let list = instruction.register_list();
    let rn   = instruction.reg_8();

    let num_regs = list.count_ones();
    let mut addr = cpu.reg(rn);

    // If Rn is present in the list the final value is the loaded
    // value, not the writeback.
    let end_address = addr + 4 * num_regs;

    cpu.set_reg(rn, end_address);

    for i in 0..8 {
        if ((list >> i) & 1) != 0 {
            let reg = RegisterIndex(i);

            let val = cpu.load::<Word>(debugger, addr);

            cpu.set_reg(reg, val);

            addr = addr.wrapping_add(4);
        }
    }
}

fn op340_beq(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if cpu.z() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op344_bne(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if !cpu.z() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op348_bcs(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if cpu.c() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op34c_bcc(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if !cpu.c() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op350_bmi(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if cpu.n() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op354_bpl(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if !cpu.n() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op360_bhi(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if cpu.c() && !cpu.z() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op364_bls(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if !cpu.c() || cpu.z() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op368_bge(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if cpu.n() == cpu.v() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op36c_blt(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if cpu.n() != cpu.v() {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op370_bgt(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if !cpu.z() && (cpu.n() == cpu.v()) {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op374_ble(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm8() << 1;

    if cpu.z() || (cpu.n() != cpu.v()) {
        let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

        cpu.set_pc(pc);
    }
}

fn op37c_swi(_: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    cpu.swi()
}

fn op38x_b(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset = instruction.signed_imm11() << 1;

    let pc = cpu.reg(RegisterIndex(15)).wrapping_add(offset);

    cpu.set_pc(pc);
}

fn op3cx_bl_hi(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    // This instruction is coded on two successive half words. The
    // reference manual says that it's implementation defined
    // whether interrupts can happen between the two
    // instructions. The behaviour as also unpredictable if the
    // pair is broken somehow. I'm not really sure how to handle
    // all the corner cases here, I'd need to run some tests to
    // figure out how the ARM7TDMI behaves exactly. This
    // implementation seems simple enough that it migh very well
    // be exactly how the real hardware handles it.
    let offset_hi = instruction.signed_imm11() << 12;

    // The offset is based on the value of the PC register during
    // the 1st instruction
    let partial_target = cpu.reg(RegisterIndex(15)).wrapping_add(offset_hi);

    // The partial target branch is stored in RL
    cpu.set_reg(RegisterIndex(14), partial_target)
}

fn op3ex_bl_lo(instruction: Instruction, _: &mut Debugger, cpu: &mut Cpu) {
    let offset_lo = instruction.b_imm_offset_11() << 1;

    let target = cpu.reg(RegisterIndex(14)).wrapping_add(offset_lo);

    let ra = cpu.next_pc | 1;

    cpu.set_reg(RegisterIndex(14), ra);

    cpu.set_pc(target);
}

static OPCODE_LUT: [fn (Instruction, &mut Debugger, &mut Cpu); 1024] = [
    // 0x000
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,

    // 0x010
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,
    op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5, op00x_lsl_ri5,

    // 0x020
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,

    // 0x030
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,
    op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5, op02x_lsr_ri5,

    // 0x040
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,

    // 0x050
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,
    op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5, op04x_asr_ri5,

    // 0x060
    op06x_add_rr, op06x_add_rr, op06x_add_rr, op06x_add_rr,
    op06x_add_rr, op06x_add_rr, op06x_add_rr, op06x_add_rr,
    op06x_sub_rr, op06x_sub_rr, op06x_sub_rr, op06x_sub_rr,
    op06x_sub_rr, op06x_sub_rr, op06x_sub_rr, op06x_sub_rr,

    // 0x070
    op07x_add_i3, op07x_add_i3, op07x_add_i3, op07x_add_i3,
    op07x_add_i3, op07x_add_i3, op07x_add_i3, op07x_add_i3,
    op07x_sub_i3, op07x_sub_i3, op07x_sub_i3, op07x_sub_i3,
    op07x_sub_i3, op07x_sub_i3, op07x_sub_i3, op07x_sub_i3,

    // 0x080
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,

    // 0x090
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,
    op08x_mov_i8, op08x_mov_i8, op08x_mov_i8, op08x_mov_i8,

    // 0x0a0
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,

    // 0x0b0
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,
    op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8, op0ax_cmp_i8,

    // 0x0c0
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,

    // 0x0d0
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,
    op0cx_add_i8, op0cx_add_i8, op0cx_add_i8, op0cx_add_i8,

    // 0x0e0
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,

    // 0x0f0
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,
    op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8, op0ex_sub_i8,

    // 0x100
    op100_and, op101_eor, op102_lsl_r, op103_lsr_r,
    op104_asr_r, op105_adc_rr, unimplemented, op107_ror,
    op108_tst, op109_neg, op10a_cmp, op10b_cmn,
    op10c_orr, op10d_mul, op10e_bic, op10f_mvn,

    // 0x110
    unimplemented, op111_add_hi, op111_add_hi, op111_add_hi,
    unimplemented, op115_cmp_hi, unimplemented, unimplemented,
    op118_cpy, op118_cpy, op118_cpy, op118_cpy,
    op11c_bx, op11c_bx, unimplemented, unimplemented,

    // 0x120
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,

    // 0x130
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,
    op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc, op12x_ldr_pc,

    // 0x140
    op14x_str_rr, op14x_str_rr, op14x_str_rr, op14x_str_rr,
    op14x_str_rr, op14x_str_rr, op14x_str_rr, op14x_str_rr,
    op14x_strh_rr, op14x_strh_rr, op14x_strh_rr, op14x_strh_rr,
    op14x_strh_rr, op14x_strh_rr, op14x_strh_rr, op14x_strh_rr,

    // 0x150
    op15x_strb_rr, op15x_strb_rr, op15x_strb_rr, op15x_strb_rr,
    op15x_strb_rr, op15x_strb_rr, op15x_strb_rr, op15x_strb_rr,
    op15x_ldrsb_rr, op15x_ldrsb_rr, op15x_ldrsb_rr, op15x_ldrsb_rr,
    op15x_ldrsb_rr, op15x_ldrsb_rr, op15x_ldrsb_rr, op15x_ldrsb_rr,

    // 0x160
    op16x_ldr_rr, op16x_ldr_rr, op16x_ldr_rr, op16x_ldr_rr,
    op16x_ldr_rr, op16x_ldr_rr, op16x_ldr_rr, op16x_ldr_rr,
    op16x_ldrh_rr, op16x_ldrh_rr, op16x_ldrh_rr, op16x_ldrh_rr,
    op16x_ldrh_rr, op16x_ldrh_rr, op16x_ldrh_rr, op16x_ldrh_rr,

    // 0x170
    op17x_ldrb_rr, op17x_ldrb_rr, op17x_ldrb_rr, op17x_ldrb_rr,
    op17x_ldrb_rr, op17x_ldrb_rr, op17x_ldrb_rr, op17x_ldrb_rr,
    op17x_ldrsh_rr, op17x_ldrsh_rr, op17x_ldrsh_rr, op17x_ldrsh_rr,
    op17x_ldrsh_rr, op17x_ldrsh_rr, op17x_ldrsh_rr, op17x_ldrsh_rr,

    // 0x180
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,

    // 0x190
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,
    op18x_str_ri5, op18x_str_ri5, op18x_str_ri5, op18x_str_ri5,

    // 0x1a0
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,

    // 0x1b0
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,
    op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5, op1ax_ldr_ri5,

    // 0x1c0
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,

    // 0x1d0
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,
    op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5, op1cx_strb_ri5,

    // 0x1e0
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,

    // 0x1f0
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,
    op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5, op1ex_ldrb_ri5,

    // 0x200
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,

    // 0x210
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,
    op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5, op20x_strh_ri5,

    // 0x220
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,

    // 0x230
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,
    op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5, op22x_ldrh_ri5,

    // 0x240
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,

    // 0x250
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,
    op24x_str_sp, op24x_str_sp, op24x_str_sp, op24x_str_sp,

    // 0x260
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,

    // 0x270
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,
    op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp, op26x_ldr_sp,

    // 0x280
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,

    // 0x290
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,
    op28x_add_pc, op28x_add_pc, op28x_add_pc, op28x_add_pc,

    // 0x2a0
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,

    // 0x2b0
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,
    op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i, op2ax_add_sp_i,

    // 0x2c0
    op2c0_add_sp, op2c0_add_sp, op2c2_sub_sp, op2c2_sub_sp,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2d0
    op2d0_push, op2d0_push, op2d0_push, op2d0_push,
    op2d4_push_lr, op2d4_push_lr, op2d4_push_lr, op2d4_push_lr,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2e0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x2f0
    op2f0_pop, op2f0_pop, op2f0_pop, op2f0_pop,
    op2f4_pop_pc, op2f4_pop_pc, op2f4_pop_pc, op2f4_pop_pc,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x300
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,

    // 0x310
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,
    op30x_stmia, op30x_stmia, op30x_stmia, op30x_stmia,

    // 0x320
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,

    // 0x330
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,
    op32x_ldmia, op32x_ldmia, op32x_ldmia, op32x_ldmia,

    // 0x340
    op340_beq, op340_beq, op340_beq, op340_beq,
    op344_bne, op344_bne, op344_bne, op344_bne,
    op348_bcs, op348_bcs, op348_bcs, op348_bcs,
    op34c_bcc, op34c_bcc, op34c_bcc, op34c_bcc,

    // 0x350
    op350_bmi, op350_bmi, op350_bmi, op350_bmi,
    op354_bpl, op354_bpl, op354_bpl, op354_bpl,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x360
    op360_bhi, op360_bhi, op360_bhi, op360_bhi,
    op364_bls, op364_bls, op364_bls, op364_bls,
    op368_bge, op368_bge, op368_bge, op368_bge,
    op36c_blt, op36c_blt, op36c_blt, op36c_blt,

    // 0x370
    op370_bgt, op370_bgt, op370_bgt, op370_bgt,
    op374_ble, op374_ble, op374_ble, op374_ble,
    unimplemented, unimplemented, unimplemented, unimplemented,
    op37c_swi, op37c_swi, op37c_swi, op37c_swi,

    // 0x380
    op38x_b, op38x_b, op38x_b, op38x_b,
    op38x_b, op38x_b, op38x_b, op38x_b,
    op38x_b, op38x_b, op38x_b, op38x_b,
    op38x_b, op38x_b, op38x_b, op38x_b,

    // 0x390
    op38x_b, op38x_b, op38x_b, op38x_b,
    op38x_b, op38x_b, op38x_b, op38x_b,
    op38x_b, op38x_b, op38x_b, op38x_b,
    op38x_b, op38x_b, op38x_b, op38x_b,

    // 0x3a0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x3b0
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,
    unimplemented, unimplemented, unimplemented, unimplemented,

    // 0x3c0
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,

    // 0x3d0
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,
    op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi, op3cx_bl_hi,

    // 0x3e0
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,

    // 0x3f0
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,
    op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo, op3ex_bl_lo,
    ];
