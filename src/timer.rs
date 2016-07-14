use interrupt::{Interrupt, IrqController};
use memory::Addressable;

#[derive(RustcDecodable, RustcEncodable)]
pub struct Timer {
    enabled: bool,
    /// In order to save a few cycles I merge the pre-divider and
    /// counter value in a single counter operating at the CPU
    /// frequency. So for instance if the timer is configured with a
    /// pre-divider of 2 and a reload value of 10, `counter` will be
    /// reloaded with `((10 + 1) << 1) - 1` == 11 * 2 - 1 == 21`.
    counter: u32,
    /// Reload value after Timer reaches `0`.
    reload: u16,
    /// Timer pre-divider config: /2, /32 or /512. See `divider_shift`
    /// below.
    divider: u8,
    /// Interrupt connected to this timer.
    interrupt: Interrupt,
}

impl Timer {
    pub fn new(interrupt: Interrupt) -> Timer {
        Timer {
            enabled: false,
            counter: 0,
            reload: 0,
            divider: 0,
            interrupt: interrupt,
        }
    }

    pub fn tick(&mut self,
                irq: &mut IrqController,
                mut cpu_ticks: u32) {

        if self.enabled {
            while cpu_ticks > 0 {
                if self.counter >= cpu_ticks {
                    irq.set_raw_interrupt(self.interrupt, false);

                    self.counter -= cpu_ticks;

                    cpu_ticks = 0;
                } else {
                    cpu_ticks -= self.counter;

                    irq.set_raw_interrupt(self.interrupt, true);

                    let reload = self.reload as u32;

                    // Scale reload to integrate the divider
                    let reload = (reload + 1) << self.divider_shift();

                    self.counter = reload - 1;
                }
            }
        }
    }

    pub fn store<A: Addressable>(&mut self, offset: u32, val: u32) {
        if A::size() == 1 {
            panic!("Unhandled {}bit timer store", A::size() * 8);
        }

        match offset {
            0 => self.reload = val as u16,
            8 => self.set_mode(val as u8),
            _ => panic!("Unhandled timer register {:x}", offset),
        }
    }

    pub fn load<A: Addressable>(&self, offset: u32) -> u32 {
        if A::size() == 1 {
            panic!("Unhandled {}bit timer store", A::size() * 8);
        }

        match offset {
            _ => panic!("Unhandled timer register {:x}", offset),
        }
    }

    fn divider_shift(&self) -> u8 {
        match self.divider {
            // cpu_clk / 2
            0 => 1,
            // cpu_clk / 32
            1 => 5,
            // cpu_clk / 512
            2 => 9,
            // cpu_clk / 2
            3 => 1,
            _ => unreachable!(),
        }
    }

    fn set_mode(&mut self, val: u8) {
        let shift_prev = self.divider_shift();

        self.divider = val & 3;
        self.enabled = (val & 4) != 0;

        let shift = self.divider_shift();

        if shift < shift_prev {
            self.counter >>= shift_prev - shift;
        } else {
            self.counter += 1;
            self.counter <<= shift - shift_prev;
            self.counter += 1;
        }
    }
}
