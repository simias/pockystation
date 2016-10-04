//! PocketStation Audio DAC emulation

use rustc_serialize::{Decodable, Encodable, Decoder, Encoder};

use memory::Addressable;
use MASTER_CLOCK_HZ;

pub struct Dac {
    /// Current output sample. Not sure how many bits are used on the
    /// real hardware, No$ says 8bit but Wikipedia seems to say that
    /// it's 10bit. Won't matter much given how crappy the sound is on
    /// the real hardware anyway...
    sample: i16,
    enabled: bool,
    backend: Box<Backend>,
    /// Master clock divider
    divider: u32,
}

impl Dac {
    pub fn new(backend: Box<Backend>) -> Dac {
        Dac {
            sample: 0,
            enabled: false,
            backend: backend,
            divider: MASTER_CLOCK_DIV,
        }
    }

    pub fn tick(&mut self, mut master_ticks: u32) {

        while master_ticks > 0 {
            if self.divider >= master_ticks {
                self.divider -= master_ticks;

                master_ticks = 0;
            } else {
                master_ticks -= self.divider;

                self.divider = MASTER_CLOCK_DIV;

                // Time to generate a sample
                let sample =
                    if self.enabled {
                        self.sample
                    } else {
                        0
                    };

                self.backend.push_sample(sample);
            }
        }
    }


    pub fn store<A: Addressable>(&mut self, offset: u32, val: u32) {
        if A::size() == 1 {
            // XXX Brightis uses 16bit dac stores, test if it behaves
            // exactly like 32bit
            panic!("Unhandled {}bit DAC store", A::size() * 8);
        }

        match offset {
            0 => self.enabled = (val & 1) != 0,
            4 => self.sample = val as i16,
            _ => panic!("Unhandled DAC register {:x}", offset),
        }
    }

    pub fn load<A: Addressable>(&self, offset: u32) -> u32 {
        if A::size() != 4 {
            panic!("Unhandled {}bit DAC store", A::size() * 8);
        }

        match offset {
            0 => self.enabled as u32,
            4 => self.sample as u16 as u32,
            _ => panic!("Unhandled DAC register {:x}", offset),
        }
    }

    pub fn set_backend(&mut self, backend: Box<Backend>) {
        self.backend = backend
    }
}

impl Encodable for Dac {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        // We don't serialize the backend, it'll be up to the frontend
        // to reset it.

        s.emit_struct("Dac", 3, |s| {
            try!(s.emit_struct_field("sample", 0,
                                     |s| self.sample.encode(s)));
            try!(s.emit_struct_field("enabled", 1,
                                     |s| self.enabled.encode(s)));
            try!(s.emit_struct_field("divider", 2,
                                     |s| self.divider.encode(s)));

            Ok(())
        })
    }
}

impl Decodable for Dac {
    fn decode<D: Decoder>(d: &mut D) -> Result<Dac, D::Error> {
        d.read_struct("Dac", 3, |d| {
            let mut dac = Dac::new(Box::new(DummyBackend));

            dac.sample =
                try!(d.read_struct_field("sample",
                                         0,
                                         Decodable::decode));
            dac.enabled =
                try!(d.read_struct_field("enabled",
                                         1,
                                         Decodable::decode));
            dac.divider =
                try!(d.read_struct_field("divider",
                                         2,
                                         Decodable::decode));

            Ok(dac)
        })
    }
}

pub trait Backend {
    fn push_sample(&mut self, sample: i16);
}

struct DummyBackend;

impl Backend for DummyBackend {
    fn push_sample(&mut self, _: i16) {
    }
}

/// Technically the audio frequency could reach MASTER_CLOCK_HZ (if
/// the CPU keeps writing a new value at every cycle at max frequency)
/// but it would be pointless to have a 4MHz audio sample rate, so I
/// divide it to a more reasonable value. A value of 90 results in a
/// sample rate of around 44.4kHz, a little more than CD
/// quality. Should be more than enough.
pub const MASTER_CLOCK_DIV: u32 = 90;

/// Audio sample rate.
pub const SAMPLE_RATE_HZ: u32 = MASTER_CLOCK_HZ / MASTER_CLOCK_DIV;
