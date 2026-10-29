import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { examples } from '../public/examples.js';
import { runProgram, MAX_OUTPUT } from '../public/runtime.js';

const compiler = await WebAssembly.compile(await readFile(new URL('../dist/evergreen-compiler.wasm', import.meta.url)));

test('the three core idea snippets verify and compile as displayed', async () => {
  const html = await readFile(new URL('../public/index.html', import.meta.url), 'utf8');
  const snippets = [...html.matchAll(/<code data-example="([^"]+)">([\s\S]*?)<\/code>/g)];
  assert.equal(snippets.length, 3);
  for (const [, name, encoded] of snippets) {
    const code = encoded.replaceAll('&gt;', '>').replaceAll('&lt;', '<').replaceAll('&amp;', '&');
    const source = name === 'contracts' ? `${code} fn main() {}` : `fn main() {${code}}`;
    const { metadata } = await compile(source);
    assert.equal(metadata.ok, true, `${name}: ${JSON.stringify(metadata)}`);
  }
});

async function compile(source) {
  const { exports } = await WebAssembly.instantiate(compiler, {});
  const bytes = new TextEncoder().encode(source);
  const pointer = exports.evg_source_resize(bytes.length);
  assert.notEqual(pointer, 0);
  new Uint8Array(exports.memory.buffer, pointer, bytes.length).set(bytes);
  exports.evg_compile();
  const metadata = JSON.parse(new TextDecoder().decode(new Uint8Array(exports.memory.buffer, exports.evg_metadata_ptr(), exports.evg_metadata_len())));
  const module = new Uint8Array(exports.memory.buffer, exports.evg_module_ptr(), exports.evg_module_len()).slice();
  return { metadata, module };
}

async function execute(source) {
  const { metadata, module } = await compile(source);
  assert.equal(metadata.ok, true, JSON.stringify(metadata));
  assert.equal(WebAssembly.validate(module), true);
  return { ...await runProgram(module, metadata.resultKind), metadata };
}

test('the three playground examples use the real compiler', async () => {
  assert.deepEqual(Object.keys(examples), ['hello', 'nonzero', 'error']);
  const hello = await execute(examples.hello);
  assert.equal(hello.output, 'Hello, Evergreen!\n');
  assert.equal((await execute(examples.nonzero)).result, '0');
  assert.equal((await compile(examples.nonzero.replace('new(10)', 'new(0)'))).metadata.ok, false);
  assert.equal((await compile(examples.error)).metadata.ok, false);
  assert.equal((await execute(examples.error.replace('increment(usize::MAX)', 'increment(41)'))).result, '42');
});

test('browser diagnostics include source excerpts, requirement locations, and proof help', async () => {
  const { metadata, module } = await compile(examples.error);
  assert.equal(metadata.ok, false);
  assert.equal(module.length, 0);
  assert.match(metadata.error, /error:/);
  assert.match(metadata.error, /--> main\.evg:\d+:\d+/);
  assert.match(metadata.error, /increment\(usize::MAX\)/);
  assert.match(metadata.error, /\^+/);
  assert.match(metadata.error, /precondition declared at main\.evg:/);
  assert.match(metadata.error, /help: supply stronger facts/);
  assert.doesNotMatch(metadata.error, /\u001b\[/);
});

test('the Wasm ABI preserves unsigned 64-bit, signed, Boolean, unit, and UTF-8 output', async () => {
  for (const [source, expected] of [
    ['fn main() -> usize {usize::MAX}', '18446744073709551615'],
    ['fn main() -> isize {isize::MIN}', '-9223372036854775808'],
    ['fn main() -> bool {let n: usize = usize::MAX; n > 42}', 'true'],
    ['fn main() -> bool {let n: isize = -42; n < 0}', 'true'],
    ['fn main() {}', '()'],
    ['fn main() -> i8 {let x: i8 = -17; let p = &x; *p}', '-17'],
  ]) assert.equal((await execute(source)).result, expected);
  const { output } = await execute('fn main() {console::print(&"λ🌲\\0"); console::print(&"");}');
  assert.equal(output, 'λ🌲\0');
});

test('borrowed byte writes use the same live storage, literals have separate storage', async () => {
  const result = await execute('fn main() {let text = "abc"; let bytes = &text; (*bytes)[1] = 90; console::println(bytes); let first = "x"; let second = "x"; let a = &first; let b = &second; (*a)[0] = 65; console::print(b);}');
  assert.equal(result.output, 'aZc\nx');
});

test('array values copy on binding and array element widths are preserved', async () => {
  assert.equal((await execute('fn main() -> u16 {let a: array(u16, 2) = [60000, 2]; let b = a; a[0] = 1; b[0]}')).result, '60000');
  assert.equal((await execute('fn read(ideal n: nat, a: &[usize; n]) -> usize where(n > 0) {(*a)[0]} fn main() -> usize {let a: array(usize, 1) = [42]; read(1, &a)}')).result, '42');
});

test('block inference preserves unsigned comparisons', async () => {
  assert.equal((await execute('fn main() -> bool {let n = {let x: usize = usize::MAX; x}; n > 0}')).result, 'true');
});

test('record constructor results are copied before subsequent calls reuse the stack', async () => {
  const source = examples.nonzero.replace('    0\n}', '    let other = NonZero::new(20);\n    my_nonzero.data\n}');
  assert.equal((await execute(source)).result, '10');
});

test('unsupported features produce target diagnostics after verification', async () => {
  for (const source of [
    'fn main() -> usize {let p: unique(usize) = alloc(42); let n = *p; drop(p); n}',
    'fn main() -> isize {linux_io::print_bytes(&"hi")}',
  ]) {
    const { metadata, module } = await compile(source);
    assert.equal(metadata.ok, false);
    assert.equal(metadata.stage, 'compile');
    assert.match(metadata.error, /WebAssembly target/);
    assert.equal(module.length, 0);
  }
});

test('loop, call depth, and console budgets stop execution, retaining prior output', async () => {
  const looping = await compile('fn main() {console::print(&"started"); while true invariant(true) {}}');
  assert.equal(looping.metadata.ok, true, JSON.stringify(looping.metadata));
  await assert.rejects(runProgram(looping.module, looping.metadata.resultKind), error => {
    assert.equal(error.output, 'started');
    assert.match(error.message, /budget/);
    return true;
  });
  const recursion = await compile('fn forever() -> usize {forever()} fn main() -> usize {forever()}');
  assert.equal(recursion.metadata.ok, true, JSON.stringify(recursion.metadata));
  await assert.rejects(runProgram(recursion.module), /budget/);
  const verbose = await compile(`fn main() {while true invariant(true) {console::print(&"${'x'.repeat(1000)}");}}`);
  assert.equal(verbose.metadata.ok, true, JSON.stringify(verbose.metadata));
  await assert.rejects(runProgram(verbose.module), error => {
    assert.equal(error.output.length, MAX_OUTPUT);
    assert.match(error.message, /100 KB/);
    return true;
  });
});
