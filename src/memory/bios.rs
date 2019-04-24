use rustc_serialize::{Decodable, Encodable, Decoder, Encoder};

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

        // For now we only accept version J110 since it's the one
        // we've been using for our tests
        if sha256 != SHA256_J110 {
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

        // BIOS only supports 16 and 32bit acccess
        if A::size() == 1 {
            panic!("Unsupported 8bit BIOS read");
        }

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.data[offset + i] as u32) << (8 * i)
        }

        r
    }
}

impl Encodable for Bios {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        // We don't store the full BIOS image in the savestate, mainly
        // because I want to be able to share and distribute
        // savestates without having to worry about legal
        // implications. If we ever support multiple kernels we should
        // probably serialize the SHA256 to make sure we're loading
        // the correct one.

        s.emit_nil()
    }
}

impl Decodable for Bios {
    fn decode<D: Decoder>(d: &mut D) -> Result<Bios, D::Error> {
        try!(d.read_nil());

        // Create a dummy BIOS with garbage contents, the frontend
        // will have to reload it with the real kernel.
        Ok(Bios {
            data: Box::new([0xba; BIOS_SIZE]),
        })
    }
}

/// BIOS size in bytes
pub const BIOS_SIZE: usize = 16 * 1024;

/// Known good SHA256 of a PocketStation BIOS J110.
pub const SHA256_J110: [u8; 32] =
    [0x6f, 0x5a, 0xff, 0x4e, 0xc3, 0xf3, 0xde, 0x8f,
     0x08, 0xbb, 0x3d, 0x52, 0x6b, 0x53, 0x24, 0x0e,
     0xaf, 0x46, 0x6d, 0xea, 0x4d, 0xc5, 0x2a, 0x1b,
     0xe7, 0x96, 0xab, 0xa4, 0x16, 0x4a, 0xae, 0x28];

/// This is an other (I think older) version of the Pocketstation
/// BIOS. I'm not sure on which devices it was used, the
/// Pocketstations I own all came with the J110 version.
pub const SHA256_J061: [u8; 32] =
    [0x67, 0x3f, 0xa1, 0xcc, 0x87, 0xed, 0x98, 0x58,
     0x05, 0x38, 0x7d, 0x1c, 0xf6, 0xb5, 0x45, 0xb7,
     0x78, 0x2f, 0x06, 0x56, 0x53, 0x82, 0xbf, 0xc9,
     0x2d, 0x75, 0xea, 0x1e, 0xb2, 0x0f, 0x1a, 0x9a];
