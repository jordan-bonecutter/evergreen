// Host ABI for Evergreen's emitted modules. No filesystem, network, or WASI.
export const MAX_OUTPUT = 100_000;

export async function runProgram(bytes, resultKind = 'signed') {
  let instance;
  let length = 0;
  const chunks = [];
  const output = () => {
    const all = new Uint8Array(length);
    let offset = 0;
    for (const chunk of chunks) { all.set(chunk, offset); offset += chunk.length; }
    return new TextDecoder().decode(all);
  };
  try {
    ({ instance } = await WebAssembly.instantiate(bytes, {
      evergreen: {
        console_write(count, pointer) {
          const memory = instance?.exports.memory;
          if (!memory || count < 0n || pointer < 0n || pointer > 0xffffffffn
              || count > BigInt(MAX_OUTPUT - length)
              || pointer + count > BigInt(memory.buffer.byteLength)) {
            throw new Error('Console output exceeded its 100 KB limit or memory bounds.');
          }
          const chunk = new Uint8Array(memory.buffer, Number(pointer), Number(count)).slice();
          chunks.push(chunk);
          length += chunk.length;
          return 0n; // Evergreen unit
        },
      },
    }));
    const value = instance.exports.main();
    const result = resultKind === 'unit' ? '()'
      : resultKind === 'bool' ? String(value !== 0n)
      : resultKind === 'unsigned' ? BigInt.asUintN(64, value).toString()
      : value.toString();
    return { output: output(), result };
  } catch (cause) {
    const error = new Error(cause instanceof WebAssembly.RuntimeError
      ? `Execution stopped: ${cause.message}. The program may have reached its call, memory, or execution budget.`
      : cause.message ?? String(cause));
    error.output = output();
    throw error;
  }
}
