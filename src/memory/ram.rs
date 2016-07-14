use rustc_serialize::{Decodable, Encodable, Decoder, Encoder};

use super::Addressable;

pub struct Ram {
    data: Box<[u8; RAM_SIZE]>,
}

impl Ram {
    pub fn new() -> Ram {
        Ram {
            data: box_array![0xca; RAM_SIZE],
        }
    }

    pub fn load<A: Addressable>(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        let mut r = 0;

        for i in 0..A::size() as usize {
            r |= (self.data[offset + i] as u32) << (8 * i)
        }

        r
    }

    pub fn store<A: Addressable>(&mut self, offset: u32, val: u32) {
        let offset = offset as usize;

        for i in 0..A::size() as usize {
            self.data[offset + i] = (val >> (i * 8)) as u8;
        }
    }
}

impl Encodable for Ram {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {

        s.emit_seq(RAM_SIZE, |s| {
            for (i, b) in self.data.iter().enumerate() {
                try!(s.emit_seq_elt(i, |s| b.encode(s)));
            }
            Ok(())
        })
    }
}

impl Decodable for Ram {
    fn decode<D: Decoder>(d: &mut D) -> Result<Ram, D::Error> {

        d.read_seq(|d, len| {
            if len != RAM_SIZE {
                return Err(d.error("wrong RAM length"));
            }

            let mut ram = Ram::new();

            for (i, b) in ram.data.iter_mut().enumerate() {
                *b = try!(d.read_seq_elt(i, Decodable::decode))
            }

            Ok(ram)
        })
    }
}

/// RAM size in bytes
const RAM_SIZE: usize = 2 * 1024;
