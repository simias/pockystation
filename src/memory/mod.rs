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

        if region != 0 && region != 4 {
            panic!("unhandled load address 0x{:08x}", addr);
        }

        let addr = (addr & 0xffffff) as usize;

        let b0 = self.kernel[addr] as u32;
        let b1 = self.kernel[addr + 1] as u32;
        let b2 = self.kernel[addr + 2] as u32;
        let b3 = self.kernel[addr + 3] as u32;

        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
    }
}
