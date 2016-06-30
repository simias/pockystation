pub struct Interconnect {
    kernel: Vec<u8>,
    /// When true the kernel is mirrored at address 0. Set on reset so
    /// that the reset vector starts executing from the kernel.
    kernel_at_0: bool,
}

impl Interconnect {
    pub fn new(kernel: Vec<u8>) -> Interconnect {
        assert!(kernel.len() == 16 * 1024);

        Interconnect {
            kernel: kernel,
            kernel_at_0: true,
        }
    }

    pub fn read32(&self, addr: u32) -> u32 {
        let region = addr >> 24;
        let offset = (addr & 0xffffff) as usize;

        match region {
            0x00 =>
                if self.kernel_at_0 {
                    let b0 = self.kernel[offset] as u32;
                    let b1 = self.kernel[offset + 1] as u32;
                    let b2 = self.kernel[offset + 2] as u32;
                    let b3 = self.kernel[offset + 3] as u32;

                    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
                } else {
                    panic!("Ram access");
                },
            0x04 => {
                let b0 = self.kernel[offset] as u32;
                    let b1 = self.kernel[offset + 1] as u32;
                    let b2 = self.kernel[offset + 2] as u32;
                    let b3 = self.kernel[offset + 3] as u32;

                    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
            }
            0x0a =>
                match offset {
                    // INT_LATCH
                    0 => 0,
                    // INT_MASK
                    8 => 0,
                    _ => panic!("Unsupported register 0x{:8x}", addr),
                },
            _ => panic!("unhandled load address 0x{:08x}", addr),
        }
    }

    pub fn store8(&mut self, addr: u32, val: u32) {
        let region = addr >> 24;
        let offset = (addr & 0xffffff) as usize;

        match region {
            0x06 =>
                match offset {
                    // F_CTRL
                    0 => match val {
                        0x03 => self.kernel_at_0 = false,
                        _ => panic!("unhandled F_CTRL 0x{:08x}", val),
                    },
                    _ => panic!("unhandled store address 0x{:08x}", addr),
                },
            _ => panic!("unhandled store address 0x{:08x}", addr),
        }
    }
}
