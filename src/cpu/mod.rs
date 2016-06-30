use std::fmt;
use memory::Interconnect;

mod armv4_is;

pub struct Cpu {
    /// Negative condition flag
    n: bool,
    /// Zero condition flag
    z: bool,
    /// Carry condition flag
    c: bool,
    /// Overflow condition flag
    v: bool,
    /// Registers. Register 15 is the PC.
    registers: [u32; 16],
    /// PC of the next instruction to be executed
    next_pc: u32,
    /// Interconnect to the memory
    inter: Interconnect,
}

impl Cpu {
    pub fn new(inter: Interconnect) -> Cpu {
        let mut cpu =
            Cpu {
                // condition flags and general purpose registers are
                // undefined on reset
                n: false,
                z: false,
                c: false,
                v: false,
                registers: [0xdeadbeef; 16],
                next_pc: 0,
                inter: inter,
            };

        // Reset vector
        cpu.set_pc(0);

        cpu
    }

    pub fn run_next_instruction(&mut self) {
        // XXX handle thumb mode
        println!("{:?}", self);

        let pc = self.next_pc;

        self.next_pc = self.registers[15];
        self.registers[15] += 4;

        if pc & 3 != 0 {
            panic!("Unaligned PC! {:?}", self);
        }

        let instruction = self.inter.read32(pc);

        println!("Executing 0x{:08x}", instruction);

        armv4_is::execute(self, instruction);
    }

    fn set_thumb(&mut self, thumb: bool) {
        if thumb {
            panic!("Switch to Thumb mode");
        }
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

    fn set_pc(&mut self, pc: u32) {
        self.next_pc = pc;
        self.registers[15] = pc + 4
    }

    fn load32(&mut self, addr: u32) -> u32 {
        if addr & 3 != 0 {
            panic!("Unaligned load32! 0x{:08x} {:?}", addr, self);
        }

        println!("load {:08x}", addr);

        self.inter.read32(addr)
    }

    fn store32(&mut self, addr: u32, val: u32) {
        if addr & 3 != 0 {
            panic!("Unaligned store32! 0x{:08x} {:?}", addr, self);
        }

        panic!("store32 0x{:08x} @ 0x{:08x}", val, addr);
    }

    fn store8(&mut self, addr: u32, val: u32) {
        self.inter.store8(addr, val);
    }
}

impl fmt::Debug for Cpu {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "PC:  0x{:08x}", self.next_pc));

        for i in 0..10 {
            try!(write!(f, "R{}:  0x{:08x}", i, self.registers[i]));

            if i % 2 == 0 {
                try!(write!(f, "  "));
            } else {
                try!(write!(f, "\n"));
            }
        }

        for i in 10..15 {
            try!(write!(f, "R{}: 0x{:08x}", i, self.registers[i]));

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
