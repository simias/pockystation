//! PocketStation infrared I/O emulation

use memory::Addressable;

pub struct Irda {
    mode: u8,
    led_on: bool,
}

impl Irda {
    pub fn new() -> Irda {
        Irda {
            mode: 0,
            led_on: false,
        }
    }

    pub fn store<A: Addressable>(&mut self, offset: u32, val: u32) {
        if A::size() != 4 {
            panic!("Unhandled {}bit IrDA store", A::size() * 8);
        }

        match offset {
            0 => self.mode = val as u8,
            4 => self.led_on = (val & 1) != 0,
            _ => panic!("Unhandled IrDA register {:x}", offset),
        }
    }

    pub fn load<A: Addressable>(&self, offset: u32) -> u32 {
        if A::size() != 4 {
            panic!("Unhandled {}bit IrDA store", A::size() * 8);
        }

        match offset {
            0 => self.mode as u32,
            4 => self.led_on as u32,
            _ => panic!("Unhandled IrDA register {:x}", offset),
        }
    }
}
