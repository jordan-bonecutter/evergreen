//! Linux x86-64 register ABI for explicitly trusted source declarations.

use super::*;

impl Emitter<'_> {
    pub(super) fn console_write(&mut self, function: &Function) -> Result<()> {
        let params = function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
            .collect::<Vec<_>>();
        self.load(&params[0].0)?;
        self.code.extend([0x48, 0x89, 0xc2]); // rdx = length
        self.load(&params[1].0)?;
        self.code.extend([0x48, 0x89, 0xc6]); // rsi = bytes
        self.code
            .extend([0xbf, 1, 0, 0, 0, 0xb8, 1, 0, 0, 0, 0x0f, 0x05]);
        self.code.extend([0x31, 0xc0]); // unit result
        Ok(())
    }

    pub(super) fn syscall(&mut self, function: &Function, number: u32) -> Result<()> {
        // Loading a binding uses rax only, so earlier argument registers survive.
        for (index, (name, _)) in function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
            .enumerate()
        {
            self.load(name)?;
            self.code.extend(match index {
                0 => &[0x48, 0x89, 0xc7][..], // rdi
                1 => &[0x48, 0x89, 0xc6],     // rsi
                2 => &[0x48, 0x89, 0xc2],     // rdx
                3 => &[0x49, 0x89, 0xc2],     // r10
                4 => &[0x49, 0x89, 0xc0],     // r8
                5 => &[0x49, 0x89, 0xc1],     // r9
                _ => return Err("Linux syscalls accept at most six arguments".into()),
            });
        }
        self.code.push(0xb8); // eax = syscall number
        self.code.extend(number.to_le_bytes());
        self.code.extend([0x0f, 0x05]); // clobbers rcx and r11; result in rax
        Ok(())
    }
}
