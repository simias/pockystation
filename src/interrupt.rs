use memory::Addressable;

pub struct IrqController {
    /// Raw interrupt signal levels
    raw: u16,
    /// Latched IRQ signal, set to one when one of the raw signals
    /// transit from 0 to 1. Reset to 0 when acknowledged (and maybe
    /// in other situations?)
    latch: u16,
    /// Interrupt mask
    mask: u16,
}

impl IrqController {
    pub fn new() -> IrqController {
        IrqController {
            raw: 0,
            latch: 0,
            mask: 0,
        }
    }

    pub fn irq_pending(&self) -> bool {
        (self.latch & self.mask & Interrupt::irq_mask()) != 0
    }

    pub fn store<A: Addressable>(&mut self, offset: u32, val: u32) {
        if A::size() == 1 {
            panic!("Unhandled {}bit IRQ store", A::size() * 8);
        }

        // IRQ registers are 16bit wide
        let val = val as u16;

        match offset {
            // Interrupt mask set
            0x08 => self.mask |= val,
            // Interrupt mask clear
            0x0c => self.mask &= !val,
            // Interrupt acknowledge
            0x10 => self.latch &= !val,
            _ => panic!("Unhandled IRQ register {:x}", offset),
        }
    }

    pub fn load<A: Addressable>(&self, offset: u32) -> u32 {
        if A::size() == 1 {
            panic!("Unhandled {}bit IRQ store", A::size() * 8);
        }

        let r =
            match offset {
                // Interrupt latch
                0x00 => self.latch,
                // Interrupt input
                0x04 => self.raw,
                // Interrupt mask
                0x08 => self.mask,
                _ => panic!("Unhandled IRQ register {:x}", offset),
            };

        r as u32
    }

    /// Return the raw level of an interrupt
    pub fn raw_interrupt(&mut self, irq: Interrupt) -> bool {
        (self.raw & (1 << (irq as u16))) != 0
    }

    /// Return the raw level of an interrupt, latching it if it goes
    /// through a rising edge.
    pub fn set_raw_interrupt(&mut self, irq: Interrupt, level: bool) {
        println!("set raw interrupt! {:?} {}", irq, level);

        let mask = 1 << (irq as u16);

        if level == true {
            if !self.raw_interrupt(irq) {
                // Rising edge
                self.latch |= mask;
            }

            self.raw |= mask;
        } else {
            self.raw &= !mask;
        }
    }
}

#[allow(dead_code)]
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Interrupt {
    /// [IRQ] "action" button (the big one on the right)
    ActionButton = 0,
    /// [IRQ] Right directional button
    RightButton = 1,
    /// [IRQ] Left directional button
    LeftButton = 2,
    /// [IRQ] Down directional button
    DownButton = 3,
    /// [IRQ] Up directional button
    UpButton = 4,
    /// [FIQ] COM interrupt
    Com = 6,
    /// [IRQ] Timer 0
    Timer0 = 7,
    /// [IRQ] Timer 1
    Timer1 = 8,
    /// [IRQ] Real time clock
    Rtc = 9,
    /// [IRQ] Battery low interrupt
    BatteryLow = 10,
    /// [IRQ] Triggered when the PocketStation is docked into the
    /// PlayStation
    Docked = 11,
    /// [IRQ] Infrared interrupt
    Irda = 12,
    /// [FIQ] Timer 2
    Timer2 = 13,
}

impl Interrupt {
    fn fiq_mask() -> u16 {
        (1 << (Interrupt::Com as u16)) | (1 << (Interrupt::Timer2 as u16))
    }

    fn irq_mask() -> u16 {
        !Interrupt::fiq_mask()
    }
}
