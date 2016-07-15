use rustc_serialize::{Decodable, Encodable, Decoder, Encoder};

use super::Addressable;

#[derive(RustcDecodable, RustcEncodable)]
pub struct Flash {
    data: Data,
    /// When true the BIOS is mirrored at address 0. Set on reset so
    /// that the reset vector starts executing from the BIOS.
    bios_at_0: bool,
    /// Physical bank enable bits.
    phys_bank_en: u16,
    /// Physical-to-virtual bank mapping. None if the virtual bank is
    /// not mapped.
    phys_to_virt_bank: [u8; 16],
    /// Virtual-to-physical bank mapping. None if the virtual bank is
    /// not mapped.
    virt_to_phys_bank: [Option<u8>; 16],
    f_wait1: u8,
    f_wait2: u8,
    f_ctrl: u8,
}

impl Flash {
    pub fn new(flash: &[u8]) -> Option<Flash> {
        if flash.len() != FLASH_SIZE {
            return None;
        }

        let mut data = box_array![0; FLASH_SIZE];

        for (d, &v) in data.iter_mut().zip(flash) {
            *d = v;
        }

        Some(Flash {
            data: Data(data),
            bios_at_0: true,
            phys_bank_en: 0,
            phys_to_virt_bank: [0; 16],
            virt_to_phys_bank: [None; 16],
            f_wait1: 0,
            f_wait2: 0,
            f_ctrl: 0,
        })
    }

    pub fn reset(&mut self) {
        self.bios_at_0 = true;
    }

    pub fn load_config<A: Addressable>(&self, offset: u32) -> u32 {

        match offset {
            // The BIOS expects bit 0 to be set, otherwise it gets
            // stuck in a strang loop waiting for R0 to become 1 (but
            // it doesn't actually load anything in R0 in the loop, so
            // I don't understand how it's ever supposed to exit
            // it). This loop is at offset 0x2e16 and 0x2e18 in the
            // BIOS.
            //
            // XXX Run tests on real hardware to figure out what's
            // read from here exactly.
            0x00 => (self.f_ctrl | 1) as u32,
            0x08 => self.phys_bank_en as u32,
            // F_CAL. XXX Need to dump a value from a real
            // PocketStation.
            0x308 => 0xca1,
            _ => panic!("Unhandled flash config register {:x}", offset),
        }
    }

    pub fn store_config<A: Addressable>(&mut self, offset: u32, val: u32) {

        match offset {
            0x00 => self.set_f_ctrl::<A>(val),
            0x08 => {
                self.phys_bank_en = val as u16;
                self.rebuild_virt_mapping();
            }
            0x0c => self.f_wait1 = val as u8,
            0x10 => self.f_wait2 = val as u8,
            0x100...0x13c => {
                let phys_bank = (offset & 0x3f) >> 2;
                let virt_bank = val & 0xf;

                self.phys_to_virt_bank[phys_bank as usize] = virt_bank as u8;

                self.rebuild_virt_mapping();
            }
            _ => panic!("Unhandled flash config register {:x}", offset),
        }
    }

    pub fn load_raw<A: Addressable>(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.data[offset + i] as u32) << (8 * i)
        }

        r
    }

    pub fn load_virtual<A: Addressable>(&self, offset: u32) -> u32 {
        // Resolve the physical bank (each bank is 8KB)
        let virt_bank = offset >> 13;
        let bank_off = offset & 0x1fff;

        match self.virt_to_phys_bank[virt_bank as usize] {
            Some(p) => {
                let phys = ((p as u32) << 13) | bank_off;

                self.load_raw::<A>(phys)
            }
            None => panic!("read from unmapped virtual bank {}", virt_bank),
        }
    }

    pub fn bios_at_0(&self) -> bool {
        self.bios_at_0
    }

    pub fn data(&self) -> &Data {
        &self.data
    }

    pub fn set_data(&mut self, data: Data) {
        self.data = data
    }

    fn set_f_ctrl<A: Addressable>(&mut self, val: u32) {
        self.f_ctrl = val as u8;

        if val == 0x03 {
            self.bios_at_0 = false;
        }
    }

    fn rebuild_virt_mapping(&mut self) {
        // XXX this is mostly guesswork, I don't know exactly what
        // happens when two different physical banks are mapped to the
        // same virtual one, I don't know how the enable bits are
        // handled exactly.

        self.virt_to_phys_bank = [None; 16];

        for (p, &v) in self.phys_to_virt_bank.iter().enumerate() {
            // Check if the bank is enabled
            if (self.phys_bank_en & (1u16 << p)) != 0 {
                let vbank = &mut self.virt_to_phys_bank[v as usize];

                match vbank {
                    &mut None => *vbank = Some(p as u8),
                    &mut Some(other) =>
                        panic!("Virtual bank {} is mapped twice: {} and {}",
                               v, other, p)
                }
            }
        }
    }
}

/// Wrapper around the raw flash contents for serialization
pub struct Data(Box<[u8; FLASH_SIZE]>);

impl ::std::ops::Deref for Data {
    type Target = [u8; FLASH_SIZE];

    fn deref(&self) -> &[u8; FLASH_SIZE] {
        &self.0
    }
}

impl Encodable for Data {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        // I'm not really sure what to do here, storing the entire
        // flash contents in a savestate is probably a bad idea since
        // you'd lose all progress if you load an old save, especially
        // if you use the same memory card image to play the game on a
        // PlayStation emu. I guess savestates should be used with a
        // lot of precautions with this emulator...
        s.emit_nil()
    }
}

impl Decodable for Data {
    fn decode<D: Decoder>(d: &mut D) -> Result<Data, D::Error> {
        try!(d.read_nil());

        // Create a dummy FLASH with garbage contents, the frontend
        // will have to reload it with the real contents.
        Ok(Data(Box::new([0xba; FLASH_SIZE])))
    }
}

impl ::std::clone::Clone for Data {
    fn clone(&self) -> Data {
        let mut data = box_array![0u8; FLASH_SIZE];

        for (a, b) in data.iter_mut().zip(self.0.iter()) {
            *a = *b;
        }

        Data(data)
    }
}

/// FLASH size in bytes
pub const FLASH_SIZE: usize = 128 * 1024;
