pub struct Interconnect {
    kernel: Vec<u8>,
}

impl Interconnect {
    pub fn new(kernel: Vec<u8>) -> Interconnect {
        assert!(kernel.len() == 16 * 1024);

        Interconnect {
            kernel: kernel,
        }
    }

    pub fn read32(&self, addr: u32) -> u32 {
        let region = addr >> 24;
        let offset = (addr & 0xffffff) as usize;

        if region == 0xa {
            return
                match offset {
                    // INT_LATCH
                    0 => 0,
                    // INT_MASK
                    8 => 0,
                    _ => panic!("Unsupported register 0x{:8x}", addr),
                };
        }

        if region != 0 && region != 4 {
            panic!("unhandled load address 0x{:08x}", addr);
        }

        let b0 = self.kernel[offset] as u32;
        let b1 = self.kernel[offset + 1] as u32;
        let b2 = self.kernel[offset + 2] as u32;
        let b3 = self.kernel[offset + 3] as u32;

        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
    }
}
