use std::fs::File;
use std::io::Read;

mod cpu;
mod memory;

fn main() {
    let args: Vec<_> = ::std::env::args().collect();

    let mut kernel = File::open(&args[1]).unwrap();

    let mut kernel_data = Vec::new();

    kernel.read_to_end(&mut kernel_data).unwrap();

    let inter = memory::Interconnect::new(kernel_data);

    let mut cpu = cpu::Cpu::new(inter);

    loop {
        cpu.run_next_instruction();
    }
}

