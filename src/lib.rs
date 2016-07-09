#[macro_use]
mod box_array;

pub mod cpu;
pub mod memory;
pub mod lcd;
mod interrupt;
mod dac;
mod irda;
mod rtc;
mod timer;

extern crate shaman;

/// Maximal frequency of the CPU, this clock can be shifted left by a
/// factor 0...7 to give the effective CPU frequency.
pub const MASTER_CLOCK_HZ: u32 = 31232 << 7;

/// Sound sample rate. Technically it could be MASTER_CLOCK_HZ but it
/// doesn't really make much sense to allow for such high frequencies,
/// it would just increase the emulation load for no gain.
pub const DAC_SAMPLE_RATE: u32 = MASTER_CLOCK_HZ / 64;
