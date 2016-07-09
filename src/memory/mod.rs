use interrupt::{Interrupt, IrqController};
use lcd::Lcd;
use dac::Dac;
use irda::Irda;
use rtc::Rtc;
use timer::Timer;

use self::bios::Bios;
use self::flash::Flash;

pub mod bios;
pub mod flash;

pub struct Interconnect {
    bios: Bios,
    flash: Flash,
    /// When true the BIOS is mirrored at address 0. Set on reset so
    /// that the reset vector starts executing from the BIOS.
    bios_at_0: bool,
    ram: Box<[u8; RAM_SIZE]>,
    irq_controller: IrqController,
    timers: [Timer; 3],
    rtc: Rtc,
    lcd: Lcd,
    dac: Dac,
    irda: Irda,
    cpu_clk_div: u8,
    frame_ticks: u32,
}

impl Interconnect {
    pub fn new(bios: Bios, flash: Flash) -> Interconnect {
        Interconnect {
            bios: bios,
            flash: flash,
            bios_at_0: true,
            ram: box_array![0xca; RAM_SIZE],
            irq_controller: IrqController::new(),
            timers: [Timer::new(Interrupt::Timer0),
                     Timer::new(Interrupt::Timer1),
                     Timer::new(Interrupt::Timer2),],
            rtc: Rtc::new(),
            lcd: Lcd::new(),
            dac: Dac::new(),
            irda: Irda::new(),
            cpu_clk_div: 7,
            frame_ticks: 0,
        }
    }

    pub fn reset(&mut self) {
        self.bios_at_0 = true;
    }

    pub fn irq_pending(&self) -> bool {
        self.irq_controller.irq_pending()
    }

    pub fn frame_ticks(&self) -> u32 {
        self.frame_ticks
    }

    pub fn set_frame_ticks(&mut self, ticks: u32) {
        self.frame_ticks = ticks
    }

    pub fn lcd(&self) -> &Lcd {
        &self.lcd
    }

    pub fn irq_controller(&mut self) -> &mut IrqController {
        &mut self.irq_controller
    }

    pub fn irq_controller_mut(&mut self) -> &mut IrqController {
        &mut self.irq_controller
    }

    pub fn tick(&mut self, cpu_ticks: u32) {
        let master_ticks = cpu_ticks << self.cpu_clk_div;

        self.rtc.tick(&mut self.irq_controller, cpu_ticks, master_ticks);

        self.timers[0].tick(&mut self.irq_controller, cpu_ticks, master_ticks);
        self.timers[1].tick(&mut self.irq_controller, cpu_ticks, master_ticks);
        self.timers[2].tick(&mut self.irq_controller, cpu_ticks, master_ticks);

        self.frame_ticks += master_ticks;
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
                if self.bios_at_0 {
                    self.bios.read::<A>(offset)
                } else {
                    self.read_ram::<A>(offset)
                },
            0x04 => self.bios.read::<A>(offset),
            0x06 =>
                match offset {
                    // F_CAL. XXX Need to dump a value from a real
                    // PocketStation.
                    0x308 => 0xca1,
                    _ => unimplemented(),
                },
            0x08 => self.flash.read::<A>(offset),
            0x0a =>
                match offset {
                    0x00...0x10 => self.irq_controller.load::<A>(offset),
                    0x800000...0x800028 => {
                        let timer = (offset >> 8) & 3;

                        self.timers[timer as usize].load::<A>(offset & 0xf)
                    }
                    _ => unimplemented(),
                },
            0x0b =>
                match offset {
                    // CLK MODE: reply that the clock is ready (locked?)
                    0 => 0x10,
                    0x800000...0x80000c => self.rtc.load::<A>(offset & 0xf),
                    _ => unimplemented(),
                },
            0x0c =>
                match offset {
                    0x800000 => self.irda.load::<A>(0),
                    0x800004 => self.irda.load::<A>(4),
                    _ => unimplemented(),
                },
            0x0d =>
                match offset {
                    0...0x1ff => self.lcd.load::<A>(offset),
                    0x800010 => self.dac.load::<A>(0),
                    0x800014 => self.dac.load::<A>(4),
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
                if !self.bios_at_0 {
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
                    0x00...0x10 => self.irq_controller.store::<A>(offset, val),
                    0x800000...0x800028 => {
                        let timer = (offset >> 8) & 3;

                        self.timers[timer as usize].store::<A>(offset & 0xf,
                                                               val);
                    }
                    _ => unimplemented(),
                },
            0x0b =>
                match offset {
                    0 => self.cpu_clk_div = 7 - (val & 0x7) as u8,
                    0x800000...0x80000c => self.rtc.store::<A>(offset & 0xf,
                                                               val),
                    _ => unimplemented(),
                },
            0x0c =>
                match offset {
                    0x00 => println!("COM MODE 0x{:08x}", val),
                    0x08 => println!("COM DATA 0x{:08x}", val),
                    0x10 => println!("COM CTRL1 0x{:08x}", val),
                    0x18 => println!("COM CTRL2 0x{:08x}", val),
                    0x800000 => self.irda.store::<A>(0, val),
                    0x800004 => self.irda.store::<A>(4, val),
                    _ => unimplemented(),
                },
            0x0d =>
                match offset {
                    0...0x1ff => self.lcd.store::<A>(offset, val),
                    0x800000 => println!("IOP CTRL 0x{:08x}", val),
                    0x800004 => println!("IOP STOP 0x{:08x}", val),
                    0x800008 => println!("IOP START 0x{:08x}", val),
                    0x800010 => self.dac.store::<A>(0, val),
                    0x800014 => self.dac.store::<A>(4, val),
                    0x800020 => println!("BATT CTRL 0x{:08x}", val),
                    _ => unimplemented(),
                },
            _ => unimplemented(),
            }
    }

    fn read_ram<A: Addressable>(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.ram[offset + i] as u32) << (8 * i)
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
            self.bios_at_0 = false;
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

/// RAM size in bytes
const RAM_SIZE: usize = 2 * 1024;
