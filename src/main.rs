use std::fs::File;
use std::io::Read;

#[macro_use]
mod box_array;

mod cpu;
mod memory;
mod interrupt;
mod dac;
mod irda;
mod lcd;
mod rtc;
mod timer;

fn main() {
    let args: Vec<_> = ::std::env::args().collect();

    let mut kernel = File::open(&args[1]).unwrap();

    let mut kernel_data = Vec::new();

    kernel.read_to_end(&mut kernel_data).unwrap();

    let mut flash = File::open(&args[2]).unwrap();

    let mut flash_data = Vec::new();

    flash.read_to_end(&mut flash_data).unwrap();

    let inter = memory::Interconnect::new(kernel_data, flash_data);

    let mut cpu = cpu::Cpu::new(inter);

    loop {
        cpu.run_next_instruction();
    }
}

/// Maximal frequency of the CPU, this clock can be shifted left by a
/// factor 0...7 to give the effective CPU frequency.
const MASTER_CLOCK_HZ: u32 = 31232 << 7;
