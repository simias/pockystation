use shaman::digest::Digest;
use shaman::sha2::Sha256;

use super::Addressable;

pub struct Bios {
    data: Box<[u8; BIOS_SIZE]>,
}

impl Bios {
    pub fn new(bios: &[u8]) -> Option<Bios> {
        if bios.len() != BIOS_SIZE {
            return None;
        }

        let mut hasher = Sha256::new();

        hasher.input(bios);

        let mut sha256 = [0; 32];

        hasher.result(&mut sha256);

        if sha256 != SHA256 {
            return None;
        }

        // BIOS is valid, we can go on
        let mut data = box_array![0; BIOS_SIZE];

        for (d, &v) in data.iter_mut().zip(bios) {
            *d = v;
        }

        Some(Bios { data: data })
    }

    pub fn load<A: Addressable>(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.data[offset + i] as u32) << (8 * i)
        }

        r
    }
}

/// BIOS size in bytes
pub const BIOS_SIZE: usize = 16 * 1024;

/// Known good SHA256 of a PocketStation BIOS. Are there other
/// version out there?
pub const SHA256: [u8; 32] = [0x67, 0x3f, 0xa1, 0xcc, 0x87, 0xed, 0x98, 0x58,
                              0x05, 0x38, 0x7d, 0x1c, 0xf6, 0xb5, 0x45, 0xb7,
                              0x78, 0x2f, 0x06, 0x56, 0x53, 0x82, 0xbf, 0xc9,
                              0x2d, 0x75, 0xea, 0x1e, 0xb2, 0x0f, 0x1a, 0x9a];
