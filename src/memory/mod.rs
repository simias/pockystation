pub struct Interconnect {
    kernel: Box<[u8; KERNEL_SIZE]>,
    ram: Box<[u8; RAM_SIZE]>,
    /// When true the kernel is mirrored at address 0. Set on reset so
    /// that the reset vector starts executing from the kernel.
    kernel_at_0: bool,
}

impl Interconnect {
    pub fn new(kernel: Vec<u8>) -> Interconnect {
        assert!(kernel.len() == KERNEL_SIZE);

        let mut kernel_array = box_array![0; KERNEL_SIZE];

        for (a, &v) in kernel_array.iter_mut().zip(&kernel) {
            *a = v;
        }

        Interconnect {
            kernel: kernel_array,
            ram: box_array![0xca; RAM_SIZE],
            kernel_at_0: true,
        }
    }

    pub fn load<A: Addressable>(&self, addr: u32) -> u32 {
        let region = addr >> 24;
        let offset = addr & 0xffffff;

        if (addr & (A::size() as u32 - 1)) != 0 {
            panic!("Missaligned {}bit read at 0x{:08x}", A::size() * 8, addr);
        }

        let unimplemented =
            || panic!("unhandled load address 0x{:08x}", addr);

        match region {
            0x00 =>
                if self.kernel_at_0 {
                    self.read_kernel::<A>(offset)
                } else {
                    panic!("Ram access");
                },
            0x04 => self.read_kernel::<A>(offset),
            0x06 =>
                match offset {
                    // F_CAL. Need to dump a value from a real PocketStation.
                    0x308 => 0xca1,
                    _ => unimplemented(),
                },
            0x0a =>
                match offset {
                    // INT_LATCH
                    0 => 0,
                    // INT_MASK
                    8 => 0,
                    _ => unimplemented(),
                },
            0x0b =>
                match offset {
                    // CLK MODE: reply that the clock is ready (locked?)
                    0 => 0x10,
                    _ => unimplemented(),
                },
            _ => unimplemented(),
        }
    }

    pub fn store<A: Addressable>(&mut self, addr: u32, val: u32) {
        let region = addr >> 24;
        let offset = addr & 0xffffff;

        if (addr & (A::size() as u32 - 1)) != 0 {
            panic!("Missaligned {}bit store at 0x{:08x}",
                   A::size() * 8, addr);
        }

        let unimplemented =
            || panic!("unhandled store address 0x{:08x}", addr);

        match region {
            0x00 =>
                if !self.kernel_at_0 {
                    self.store_ram::<A>(offset, val);
                },
            0x06 =>
                match offset {
                    0x00 => self.set_f_ctrl::<A>(val),
                    0x08 => println!("F BANK FLG 0x{:08x}", val),
                    0x0c => println!("F_WAIT1 0x{:08x}", val),
                    0x10 => println!("F_WAIT2 0x{:08x}", val),
                    0x100...0x13c => {
                        let bank = (offset & 0x3f) / 4;

                        println!("F BANK VAL{} 0x{:08x}", bank, val);
                    }
                    _ => unimplemented(),
                },
            0x0a =>
                match offset {
                    0x0c => println!("INT MASK CLR 0x{:08x}", val),
                    0x08 => println!("INT MASK SET 0x{:08x}", val),
                    0x10 => println!("INT ACK 0x{:08x}", val),
                    0x800000 => println!("T0 RELOAD 0x{:08x}", val),
                    0x800008 => println!("T0 MODE 0x{:08x}", val),
                    0x800010 => println!("T1 RELOAD 0x{:08x}", val),
                    0x800018 => println!("T1 MODE 0x{:08x}", val),
                    0x800020 => println!("T2 RELOAD 0x{:08x}", val),
                    0x800028 => println!("T1 MODE 0x{:08x}", val),
                    _ => unimplemented(),
                },
            0x0b =>
                match offset {
                    0 => println!("CLK MODE 0x{:08x}", val),
                    0x800000 => println!("RTC MODE 0x{:08x}", val),
                    _ => unimplemented(),
                },
            0x0c =>
                match offset {
                    0x00 => println!("COM MODE 0x{:08x}", val),
                    0x08 => println!("COM DATA 0x{:08x}", val),
                    0x10 => println!("COM CTRL1 0x{:08x}", val),
                    0x18 => println!("COM CTRL2 0x{:08x}", val),
                    0x800000 => println!("IRDA MODE 0x{:08x}", val),
                    0x800004 => println!("IRDA DATA 0x{:08x}", val),
                    _ => unimplemented(),
                },
            0x0d =>
                match offset {
                    0x0 => println!("LCD MODE 0x{:08x}", val),
                    0x4 => println!("LCD CAL 0x{:08x}", val),
                    0x100...0x17c => {
                        let row = (offset & 0x7f) / 4;

                        println!("LCD VRAM{} 0x{:08x}", row, val);
                    },
                    0x800000 => println!("IOP CTRL 0x{:08x}", val),
                    0x800004 => println!("IOP STOP 0x{:08x}", val),
                    0x800008 => println!("IOP START 0x{:08x}", val),
                    0x800010 => println!("DAC CTRL 0x{:08x}", val),
                    0x800014 => println!("DAC DATA 0x{:08x}", val),
                    0x800020 => println!("BATT CTRL 0x{:08x}", val),
                    _ => unimplemented(),
                },
            _ => unimplemented(),
            }
    }

    fn read_kernel<A: Addressable>(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.kernel[offset + i] as u32) << (8 * i)
        }

        r
    }

    fn store_ram<A: Addressable>(&mut self, offset: u32, val: u32) {
        let offset = offset as usize;

        for i in 0..A::size() as usize {
            self.ram[offset + i] = (val >> (i * 8)) as u8;
        }
    }

    fn set_f_ctrl<A: Addressable>(&mut self, val: u32) {
        if A::size() == 1 && val == 0x03 {
            self.kernel_at_0 = false;
        } else if A::size() == 4 {
            println!("F CTRL 0x{:08x}", val);
        } else {
            panic!("unhandled F_CTRL 0x{:02x}", val);
        }
    }
}

/// Trait representing the attributes of a memory access
pub trait Addressable {
    /// Retreive the size of the access in bytes
    fn size() -> u8;
}

/// Marker for Byte (8bit) access
pub struct Byte;

impl Addressable for Byte {
    fn size() -> u8 {
        1
    }
}

/// Marker for HalfWord (16bit) access
pub struct HalfWord;

impl Addressable for HalfWord {
    fn size() -> u8 {
        2
    }
}

/// Marker for Word (32bit) access
pub struct Word;

impl Addressable for Word {
    fn size() -> u8 {
        4
    }
}

/// Kernel size in bytes
const KERNEL_SIZE: usize = 16 * 1024;

/// RAM size in bytes
const RAM_SIZE: usize = 2 * 1024;
