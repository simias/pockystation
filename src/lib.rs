#[macro_use]
mod box_array;

pub mod cpu;
pub mod memory;
mod interrupt;
mod dac;
mod irda;
mod lcd;
mod rtc;
mod timer;

/// Maximal frequency of the CPU, this clock can be shifted left by a
/// factor 0...7 to give the effective CPU frequency.
const MASTER_CLOCK_HZ: u32 = 31232 << 7;
