use std::fmt;
use std::mem::swap;

use memory::{Interconnect, Word, HalfWord, Byte};

mod armv4_is;
mod thumbv1_is;

pub struct Cpu {
    /// Negative condition flag
    n: bool,
    /// Zero condition flag
    z: bool,
    /// Carry condition flag
    c: bool,
    /// Overflow condition flag
    v: bool,
    /// General purpose registers for the current mode. Register 15 is
    /// the PC.
    registers: [u32; 16],
    /// Banked LR and SP registers for the user and system modes
    user_system_bank: [u32; 2],
    /// Banked SPSR, LR and SP registers for the supervisor mode
    supervisor_bank: [u32; 3],
    /// Banked SPSR, LR and SP registers for the abort mode
    abort_bank: [u32; 3],
    /// Banked SPSR, LR and SP registers for the undefined mode
    undefined_bank: [u32; 3],
    /// Banked SPSR, LR and SP registers for the IRQ mode
    irq_bank: [u32; 3],
    /// Banked SPSR, LR, SP, and R12 to R8 registers for the FIQ mode
    fiq_bank: [u32; 8],
    /// PC of the next instruction to be executed
    next_pc: u32,
    /// If true we're in Thumb mode, otherwise ARM
    thumb: bool,
    /// CPU operating mode
    mode: Mode,
    /// If `true` interrupts are enabled
    irq_en: bool,
    /// If `true` fast interrupts are enabled
    fiq_en: bool,
    /// Saved program status register
    spsr: u32,
    /// Interconnect to the memory
    inter: Interconnect,
}

impl Cpu {
    pub fn new(inter: Interconnect) -> Cpu {
        let mut cpu =
            Cpu {
                // condition flags and general purpose registers are
                // undefined on reset
                n: true,
                z: true,
                c: true,
                v: true,
                registers: [0xdeadbeef; 16],
                user_system_bank: [0; 2],
                supervisor_bank: [0; 3],
                abort_bank: [0; 3],
                undefined_bank: [0; 3],
                irq_bank: [0; 3],
                fiq_bank: [0; 8],
                next_pc: 0,
                thumb: false,
                // Supervisor mode on reset
                mode: Mode::Supervisor,
                // IRQs disabled on reset
                irq_en: false,
                // FIQs disabled on reset
                fiq_en: false,
                spsr: 0,
                inter: inter,
            };

        cpu.reset();

        cpu
    }

    pub fn reset(&mut self) {
        self.inter.reset();

        self.thumb = false;

        self.irq_en = false;
        self.fiq_en = false;

        self.change_mode(Mode::Supervisor);

        // Jump to reset vector
        self.set_pc(0);
    }

    /// Run CPU for `master_ticks` master clock periods
    pub fn run_ticks(&mut self, master_ticks: u32) {
        while self.inter.frame_ticks() < master_ticks {
            self.run_next_instruction();
        }

        self.inter.set_frame_ticks(0);
    }

    pub fn run_next_instruction(&mut self) {
        // Assume each instruction takes exactly one CPU cycle for
        // now, a gross oversimplification...
        self.inter.tick(1);

        if self.inter.irq_controller().pending() {
            // FIQs have a high priority than IRQs, so check for them
            // first
            if self.fiq_en && self.inter.irq_controller().fiq_pending() {
                self.fiq();
            } else if self.irq_en && self.inter.irq_controller().irq_pending() {
                self.irq();
            }
        }

        let pc = self.next_pc;

        self.next_pc = self.registers[15];

        if self.thumb {
            // In Thumb mode the PC register (R15) always points to
            // the current instruction's addres + 4 or unpredictable
            // depending on how it's used.
            self.registers[15] += 2;

            if pc & 1 != 0 {
                panic!("Misaligned PC! {:?}", self);
            }

            let instruction = self.inter.load::<HalfWord>(pc) as u16;

            thumbv1_is::execute(self, instruction);

        } else {
            // In ARM mode the PC register (R15) always points to the
            // current instruction's addres + 8, except for STR/STM
            // instructions that store R15 where it's implementation
            // whether it's +8 or +12. I need to check which it is for the
            // ARM7TDMI used in the PocketStation.
            self.registers[15] += 4;

            if pc & 3 != 0 {
                panic!("Misaligned PC! {:?}", self);
            }

            let instruction = self.inter.load::<Word>(pc);

            armv4_is::execute(self, instruction);
        }
    }

    pub fn interconnect(&self) -> &Interconnect {
        &self.inter
    }

    pub fn interconnect_mut(&mut self) -> &mut Interconnect {
        &mut self.inter
    }

    fn n(&self) -> bool {
        self.n
    }

    fn set_n(&mut self, n: bool) {
        self.n = n
    }

    fn z(&self) -> bool {
        self.z
    }

    fn set_z(&mut self, z: bool) {
        self.z = z
    }

    fn c(&self) -> bool {
        self.c
    }

    fn set_c(&mut self, c: bool) {
        self.c = c
    }

    fn v(&self) -> bool {
        self.v
    }

    fn set_v(&mut self, v: bool) {
        self.v = v
    }

    fn reg(&self, r: RegisterIndex) -> u32 {
        self.registers[r.0 as usize]
    }

    fn set_reg(&mut self, r: RegisterIndex, v: u32) {
        if r.is_pc() {
            self.set_pc(v);
        } else {
            self.registers[r.0 as usize] = v;
        }
    }

    /// Some ARM opcodes write to the PC and we're supposed to ignore
    /// the two LSB (effectively word-aligning the PC no matter
    /// what). Some other opcodes aren't documented in the manual as
    /// doing that so I use `set_reg` directly for those.
    fn set_reg_pc_mask(&mut self, r: RegisterIndex, v: u32) {
        if r.is_pc() {
            self.set_pc(v & !3);
        } else {
            self.registers[r.0 as usize] = v;
        }
    }

    fn set_pc(&mut self, pc: u32) {
        self.next_pc = pc;

        let r15_offset =
            if self.thumb {
                2
            } else {
                4
            };

        self.registers[15] = pc + r15_offset;
    }

    /// Change the value of the PC update the thumb state. Since the
    /// PC register value depends on whether we're in ARM on Thumb
    /// mode (+8 or +4 respectively) it's important to change the
    /// instruction mode before we write the new PC when the mode
    /// changes, this function takes care of that.
    fn set_pc_thumb(&mut self, pc: u32, thumb: bool) {
        self.thumb = thumb;

        self.set_pc(pc);
    }

    fn set_pc_cpsr(&mut self, pc: u32, cpsr: u32) {
        let mode = Mode::from_field(cpsr & 0x1f);

        self.change_mode(mode);

        self.thumb = (cpsr & 0x20) != 0;

        self.fiq_en = (cpsr & 0x40) == 0;
        self.irq_en = (cpsr & 0x80) == 0;

        let flags = cpsr >> 28;

        self.v = (flags & 1) != 0;
        self.c = (flags & 2) != 0;
        self.z = (flags & 4) != 0;
        self.n = (flags & 8) != 0;

        self.set_pc(pc);
    }

    fn change_mode(&mut self, mode: Mode) {
        // The FIQ banking code assumes we can't bank to the same
        // mode, otherwise the non-FIQ R8-R14 could be lost.
        if self.mode == mode {
            return;
        }

        // First save the current mode's banked registers
        match self.mode {
            Mode::User | Mode::System => {
                // User mode has no SPSR
                self.user_system_bank[0] = self.registers[14];
                self.user_system_bank[1] = self.registers[13];
            },
            Mode::Supervisor => {
                self.supervisor_bank[0] = self.spsr;
                self.supervisor_bank[1] = self.registers[14];
                self.supervisor_bank[2] = self.registers[13];
            }
            Mode::Abort => {
                self.abort_bank[0] = self.spsr;
                self.abort_bank[1] = self.registers[14];
                self.abort_bank[2] = self.registers[13];
            }
            Mode::Undefined => {
                self.undefined_bank[0] = self.spsr;
                self.undefined_bank[1] = self.registers[14];
                self.undefined_bank[2] = self.registers[13];
            }
            Mode::Irq => {
                self.irq_bank[0] = self.spsr;
                self.irq_bank[1] = self.registers[14];
                self.irq_bank[2] = self.registers[13];
            }
            Mode::Fiq => {
                self.fiq_bank[0] = self.spsr;
                self.fiq_bank[1] = self.registers[14];
                self.fiq_bank[2] = self.registers[13];

                // Since only the FIQ mode banks registers R8-R12 we
                // can just swap them back and forth
                swap(&mut self.fiq_bank[3], &mut self.registers[12]);
                swap(&mut self.fiq_bank[4], &mut self.registers[11]);
                swap(&mut self.fiq_bank[5], &mut self.registers[10]);
                swap(&mut self.fiq_bank[6], &mut self.registers[9]);
                swap(&mut self.fiq_bank[7], &mut self.registers[8]);
            }
        };

        // Now we can load the banked registers for the new mode
        match mode {
            Mode::User | Mode::System => {
                self.registers[14] = self.user_system_bank[0];
                self.registers[13] = self.user_system_bank[1];
            },
            Mode::Supervisor => {
                self.spsr          = self.supervisor_bank[0];
                self.registers[14] = self.supervisor_bank[1];
                self.registers[13] = self.supervisor_bank[2];
            }
            Mode::Abort => {
                self.spsr          = self.abort_bank[0];
                self.registers[14] = self.abort_bank[1];
                self.registers[13] = self.abort_bank[2];
            }
            Mode::Undefined => {
                self.spsr          = self.undefined_bank[0];
                self.registers[14] = self.undefined_bank[1];
                self.registers[13] = self.undefined_bank[2];
            }
            Mode::Irq => {
                self.spsr          = self.irq_bank[0];
                self.registers[14] = self.irq_bank[1];
                self.registers[13] = self.irq_bank[2];
            }
            Mode::Fiq => {
                self.spsr          = self.fiq_bank[0];
                self.registers[14] = self.fiq_bank[1];
                self.registers[13] = self.fiq_bank[2];

                swap(&mut self.fiq_bank[3], &mut self.registers[12]);
                swap(&mut self.fiq_bank[4], &mut self.registers[11]);
                swap(&mut self.fiq_bank[5], &mut self.registers[10]);
                swap(&mut self.fiq_bank[6], &mut self.registers[9]);
                swap(&mut self.fiq_bank[7], &mut self.registers[8]);
            }
        };

        self.mode = mode;
    }

    /// Build the value of the 32bit CPSR register
    fn cpsr(&self) -> u32 {
        let mut r = 0u32;

        r |= self.mode as u32;
        r |= (self.thumb as u32) << 5;
        r |= ((!self.fiq_en) as u32) << 6;
        r |= ((!self.irq_en) as u32) << 7;

        r |= (self.v as u32) << 28;
        r |= (self.c as u32) << 29;
        r |= (self.z as u32) << 30;
        r |= (self.n as u32) << 31;

        r
    }

    fn spsr(&self) -> u32 {
        if self.mode.has_spsr() {
            self.spsr
        } else {
            panic!("Attempted to access SPSR in {:?} mode",
                   self.mode);
        }
    }

    /// Software interrupt, also called "SVC" (supervisor call) in
    /// modern ARM architectures.
    fn swi(&mut self) {
        let ra = self.next_pc;
        let spsr = self.cpsr();

        self.thumb = false;
        self.irq_en = false;

        self.change_mode(Mode::Supervisor);

        self.spsr = spsr;
        self.set_reg(RegisterIndex(14), ra);

        // Jump to SWI vector
        self.set_pc(0x8)
    }

    /// Fast interrupt request
    fn fiq(&mut self) {
        let ra = self.next_pc + 4;
        let spsr = self.cpsr();

        self.thumb = false;
        self.fiq_en = false;
        self.irq_en = false;

        self.change_mode(Mode::Fiq);

        self.spsr = spsr;
        self.set_reg(RegisterIndex(14), ra);

        // Jump to FIQ vector
        self.set_pc(0x1c)
    }

    /// Interrupt request
    fn irq(&mut self) {
        let ra = self.next_pc + 4;
        let spsr = self.cpsr();

        self.thumb = false;
        self.irq_en = false;

        self.change_mode(Mode::Irq);

        self.spsr = spsr;
        self.set_reg(RegisterIndex(14), ra);

        // Jump to IRQ vector
        self.set_pc(0x18)
    }

    fn msr_cpsr(&mut self, val: u32, field_mask: u32) {
        let unalloc_mask = 0x0fffff00;

        // The reference manual says it's unpredictable even if those
        // bits aren't set in the field_mask
        if val & unalloc_mask != 0 {
            panic!("Attempt to set CPSR reserved bits");
        }

        if (field_mask & 1) != 0 && self.mode.is_privileged() {
            // Set control bits
            let mode = Mode::from_field((val & 0xf) | 0x10);

            self.change_mode(mode);

            let thumb = (val & 0x20) != 0;

            if thumb {
                // MSR is unpredictable if it attempts to change the
                // execution mode.
                panic!("Attempted to switch to Thumb mode in MSR");
            }

            self.fiq_en = (val & 0x40) == 0;
            self.irq_en = (val & 0x80) == 0;
        }

        if (field_mask & 8) != 0 {
            // Set flags bits
            let flags = val >> 28;

            self.v = (flags & 1) != 0;
            self.c = (flags & 2) != 0;
            self.z = (flags & 4) != 0;
            self.n = (flags & 8) != 0;
        }
    }

    fn load32(&mut self, addr: u32) -> u32 {
        if addr & 3 != 0 {
            panic!("Unaligned load32! 0x{:08x} {:?}", addr, self);
        }

        self.inter.load::<Word>(addr)
    }

    fn store32(&mut self, addr: u32, val: u32) {
        if addr & 3 != 0 {
            panic!("Unaligned store32! 0x{:08x} {:?}", addr, self);
        }

        self.inter.store::<Word>(addr, val);
    }

    fn load16(&mut self, addr: u32) -> u16 {
        if addr & 1 != 0 {
            panic!("Unaligned load16! 0x{:08x} {:?}", addr, self);
        }

        self.inter.load::<HalfWord>(addr) as u16
    }

    fn store16(&mut self, addr: u32, val: u32) {
        if addr & 1 != 0 {
            panic!("Unaligned store16! 0x{:08x} {:?}", addr, self);
        }

        self.inter.store::<HalfWord>(addr, val);
    }

    fn load8(&mut self, addr: u32) -> u8 {
        self.inter.load::<Byte>(addr) as u8
    }

    fn store8(&mut self, addr: u32, val: u32) {
        self.inter.store::<Byte>(addr, val);
    }
}

impl fmt::Debug for Cpu {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "CPC:  0x{:08x}  Mode: {:?}",
                      self.next_pc, self.mode));

        if self.mode.has_spsr() {
            try!(writeln!(f, "CPSR: 0x{:08x}  SPSR: 0x{:08x}",
                          self.cpsr(), self.spsr));
        } else {
            try!(writeln!(f, "CPSR: 0x{:08x}", self.cpsr()));
        }

        let is =
            if self.thumb {
                "Thumb"
            } else {
                "ARM"
            };

        let flag = |f, l| if f { l } else { '-' };

        try!(writeln!(f, "{}{}{}{} {}{} {}",
                      flag(self.n, 'N'),
                      flag(self.z, 'Z'),
                      flag(self.c, 'C'),
                      flag(self.v, 'V'),
                      flag(self.irq_en, 'I'),
                      flag(self.fiq_en, 'F'),
                      is));

        for i in 0..10 {
            try!(write!(f, "R{}:   0x{:08x}", i, self.registers[i]));

            if i % 2 == 0 {
                try!(write!(f, "  "));
            } else {
                try!(write!(f, "\n"));
            }
        }

        for i in 10..16 {
            try!(write!(f, "R{}:  0x{:08x}", i, self.registers[i]));

            if i % 2 == 0 {
                try!(write!(f, "  "));
            } else {
                try!(write!(f, "\n"));
            }
        }

        Ok(())
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct RegisterIndex(u32);

impl RegisterIndex {
    fn is_pc(self) -> bool {
        self.0 == 15
    }
}

impl fmt::Display for RegisterIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_pc() {
            write!(f, "PC")
        } else {
            write!(f, "R{}", self.0)
        }
    }
}

/// CPU modes
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Mode {
    User       = 0b10000,
    Fiq        = 0b10001,
    Irq        = 0b10010,
    Supervisor = 0b10011,
    Abort      = 0b10111,
    Undefined  = 0b11011,
    System     = 0b11111,
}

impl Mode {
    fn from_field(mode: u32) -> Mode {
        match mode {
            0b10000 => Mode::User,
            0b10001 => Mode::Fiq,
            0b10010 => Mode::Irq,
            0b10011 => Mode::Supervisor,
            0b10111 => Mode::Abort,
            0b11011 => Mode::Undefined,
            0b11111 => Mode::System,
            _ => panic!("Invalid mode: {:02x}", mode),
        }
    }

    fn is_privileged(self) -> bool {
        self != Mode::User
    }

    fn has_spsr(self) -> bool {
        self != Mode::User && self != Mode::System
    }
}
