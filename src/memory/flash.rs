use super::Addressable;

pub struct Flash {
    data: Box<[u8; FLASH_SIZE]>,
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

        Some(Flash { data: data })
    }

    pub fn read<A: Addressable>(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        println!("FLASH read {:x}", offset);

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.data[offset + i] as u32) << (8 * i)
        }

        r
    }
}

/// FLASH size in bytes
pub const FLASH_SIZE: usize = 128 * 1024;
