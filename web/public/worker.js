import { runProgram } from './runtime.js';

let compiler;

async function loadCompiler() {
  const response = await fetch(new URL('./evergreen-compiler.wasm', import.meta.url));
  if (!response.ok) throw new Error(`Compiler download failed (${response.status}).`);
  compiler = await WebAssembly.compile(await response.arrayBuffer());
  self.postMessage({ type: 'ready' });
}

self.onmessage = async ({ data }) => {
  if (data.type !== 'run') return;
  const started = performance.now();
  let metadata;
  try {
    const source = new TextEncoder().encode(data.source);
    if (source.length > 100_000) throw new Error('Source exceeds the playground’s 100 KB limit.');
    self.postMessage({ type: 'phase', message: 'Checking proofs and compiling to Wasm…' });
    // Each compilation starts with fresh memory, even after a panic or failure.
    const { exports } = await WebAssembly.instantiate(compiler, {});
    const pointer = exports.evg_source_resize(source.length);
    if (!pointer) throw new Error('Could not allocate source in compiler memory.');
    new Uint8Array(exports.memory.buffer, pointer, source.length).set(source);
    exports.evg_compile();
    metadata = JSON.parse(new TextDecoder().decode(new Uint8Array(
      exports.memory.buffer, exports.evg_metadata_ptr(), exports.evg_metadata_len(),
    )));
    if (!metadata.ok) { self.postMessage({ type: 'result', ...metadata }); return; }
    const module = new Uint8Array(exports.memory.buffer, exports.evg_module_ptr(), exports.evg_module_len()).slice();
    self.postMessage({ type: 'phase', message: 'Running compiled WebAssembly…' });
    let execution;
    try { execution = await runProgram(module, metadata.resultKind); }
    catch (error) { execution = { runtimeError: error.message, output: error.output ?? '' }; }
    self.postMessage({
      type: 'result', ...metadata, ...execution,
      elapsed: Math.round(performance.now() - started), module: module.buffer,
    }, [module.buffer]);
  } catch (error) {
    self.postMessage({ type: 'result', ok: false, stage: 'compiler', error: error.message ?? String(error) });
  }
};

loadCompiler().catch(error => self.postMessage({ type: 'load-error', error: error.message }));
