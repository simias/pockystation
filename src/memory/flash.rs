use rustc_serialize::{Decodable, Encodable, Decoder, Encoder};

use super::Addressable;

#[derive(RustcDecodable, RustcEncodable)]
pub struct Flash {
    data: Data,
    /// When true the BIOS is mirrored at address 0. Set on reset so
    /// that the reset vector starts executing from the BIOS.
    bios_at_0: bool,
    bank_en: u16,
    bank_map: [u8; 16],
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
            bank_en: 0,
            bank_map: [0; 16],
            f_wait1: 0,
            f_wait2: 0,
            f_ctrl: 0,
        })
    }

    pub fn reset(&mut self) {
        self.bios_at_0 = true;
    }

    pub fn load_config<A: Addressable>(&self, offset: u32) -> u32 {
        debug!("flash load config {:x}", offset);

        match offset {
            0x00 => self.f_ctrl as u32,
            0x08 => self.bank_en as u32,
            // F_CAL. XXX Need to dump a value from a real
            // PocketStation.
            0x308 => 0xca1,
            _ => panic!("Unhandled flash config register {:x}", offset),
        }
    }

    pub fn store_config<A: Addressable>(&mut self, offset: u32, val: u32) {

        debug!("flash store config {:x}, {:x}", offset, val);

        match offset {
            0x00 => self.set_f_ctrl::<A>(val),
            0x08 => self.bank_en = val as u16,
            0x0c => self.f_wait1 = val as u8,
            0x10 => self.f_wait2 = val as u8,
            0x100...0x13c => {
                let bank = (offset & 0x3f) >> 2;

                self.bank_map[bank as usize] = (val & 0xf) as u8;
            }
            _ => panic!("Unhandled flash config register {:x}", offset),
        }
    }

    pub fn load_raw<A: Addressable>(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        println!("FLASH load raw {:x}", offset);

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.data[offset + i] as u32) << (8 * i)
        }

        r
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
