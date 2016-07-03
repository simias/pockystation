//! PocketStation Audio DAC emulator

use memory::Addressable;

pub struct Dac {
    /// Current output sample. Not sure how many bits are used on the
    /// real hardware, No$ says 8bit but Wikipedia seems to say that
    /// it's 10bit. Won't matter much given how crappy the sound is on
    /// the real hardware anyway...
    sample: i16,
    enabled: bool,
}

impl Dac {
    pub fn new() -> Dac {
        Dac {
            sample: 0,
            enabled: false,
        }
    }

    pub fn store<A: Addressable>(&mut self, offset: u32, val: u32) {
        if A::size() != 4 {
            panic!("Unhandled {}bit DAC store", A::size() * 8);
        }

        match offset {
            0 => self.enabled = (val & 1) != 0,
            4 => self.sample = val as i16,
            _ => panic!("Unhandled DAC register {:x}", offset),
        }
    }

    pub fn load<A: Addressable>(&self, offset: u32) -> u32 {
        if A::size() != 4 {
            panic!("Unhandled {}bit DAC store", A::size() * 8);
        }

        match offset {
            0 => self.enabled as u32,
            4 => self.sample as u16 as u32,
            _ => panic!("Unhandled DAC register {:x}", offset),
        }
    }
}
