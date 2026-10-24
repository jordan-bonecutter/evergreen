//! ELF64 packaging for Linux x86-64, with separate executable and stack segments.
use super::STACK;

const BASE: u64 = 0x400000;
const ELF_HEADER_BYTES: usize = 64;
const SEGMENT_HEADER_BYTES: usize = 56;
const SEGMENT_COUNT: usize = 2;
const HEADER: usize = ELF_HEADER_BYTES + SEGMENT_COUNT * SEGMENT_HEADER_BYTES;
const PAGE_BYTES: usize = 4096;
const READ: u32 = 4;
const WRITE: u32 = 2;
const EXECUTE: u32 = 1;

struct Segment {
    flags: u32,
    file_offset: usize,
    address: u64,
    file_size: usize,
    memory_size: usize,
}

impl Segment {
    fn write(&self, header: &mut [u8]) {
        header[..4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        header[4..8].copy_from_slice(&self.flags.to_le_bytes());
        for (offset, value) in [
            (8, self.file_offset as u64),
            (16, self.address),
            (24, self.address),
            (32, self.file_size as u64),
            (40, self.memory_size as u64),
            (48, PAGE_BYTES as u64),
        ] {
            header[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
}

pub(super) fn executable(mut code: Vec<u8>, stack_pointer: usize) -> Vec<u8> {
    let text_size = HEADER + code.len();
    let data_offset = (text_size + PAGE_BYTES - 1) & !(PAGE_BYTES - 1);
    let stack_end = BASE + data_offset as u64 + STACK as u64;
    code[stack_pointer..stack_pointer + 8].copy_from_slice(&stack_end.to_le_bytes());
    let segments = [
        Segment {
            flags: READ | EXECUTE,
            file_offset: 0,
            address: BASE,
            file_size: text_size,
            memory_size: text_size,
        },
        Segment {
            flags: READ | WRITE,
            file_offset: data_offset,
            address: BASE + data_offset as u64,
            file_size: 1,
            memory_size: STACK,
        },
    ];
    let mut output = header();
    for (index, segment) in segments.iter().enumerate() {
        let offset = ELF_HEADER_BYTES + index * SEGMENT_HEADER_BYTES;
        segment.write(&mut output[offset..offset + SEGMENT_HEADER_BYTES]);
    }
    output.extend(code);
    output.resize(data_offset + 1, 0);
    output
}

fn header() -> Vec<u8> {
    let mut output = vec![0u8; HEADER];
    output[..16].copy_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    output[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    output[18..20].copy_from_slice(&62u16.to_le_bytes()); // EM_X86_64
    output[20..24].copy_from_slice(&1u32.to_le_bytes()); // ELF version
    output[24..32].copy_from_slice(&(BASE + HEADER as u64).to_le_bytes()); // entry point
    output[32..40].copy_from_slice(&(ELF_HEADER_BYTES as u64).to_le_bytes());
    output[52..54].copy_from_slice(&(ELF_HEADER_BYTES as u16).to_le_bytes());
    output[54..56].copy_from_slice(&(SEGMENT_HEADER_BYTES as u16).to_le_bytes());
    output[56..58].copy_from_slice(&(SEGMENT_COUNT as u16).to_le_bytes());
    output
}
