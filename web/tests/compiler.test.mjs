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
  const unknown = await compile('fn nonzero(x: usize) where x != 0 {} fn main() {nonzero(usize::MAX + 1);}');
  assert.equal(unknown.metadata.ok, false);
  // Target aliases render as their checked primitive in reconstructed obligations.
  assert.match(unknown.metadata.error, /unproved obligation: \(\(u32::MAX \+ 1\) != 0\)/);
  assert.doesNotMatch(unknown.metadata.error, /evg_\d+/);
});

test('the Wasm ABI preserves unsigned 64-bit, signed, Boolean, unit, and UTF-8 output', async () => {
  for (const [source, expected] of [
    ['fn main() -> usize {usize::MAX}', '4294967295'],
    ['fn main() -> u64 {u64::MAX}', '18446744073709551615'],
    ['fn main() -> isize {isize::MIN}', '-2147483648'],
    ['fn main() -> i64 {i64::MIN}', '-9223372036854775808'],
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

test('refined scalars preserve their condition through construction and borrowed writes', async () => {
  const source = 'type NonZero usize where self != 0; impl Copy for NonZero {} fn id(x: NonZero) -> NonZero {x} fn main() -> usize {let n: NonZero = 42; id(n)}';
  assert.equal((await execute(source)).result, '42');
  assert.equal((await compile(source.replace('= 42', '= 0'))).metadata.ok, false);
  const array = 'type NonZero usize where self != 0; fn main() -> usize {let values: [NonZero; 2] = [20, 22]; values[0] + values[1]}';
  assert.equal((await execute(array)).result, '42');
  const borrow = 'type NonZero usize where self != 0; fn zero(x: &usize) modifies(x) ensures *x == 0 {*x = 0;} fn main() {let n: NonZero = 1; zero(&n);}';
  assert.equal((await compile(borrow)).metadata.ok, false);
});

test('unsupported features produce target diagnostics after verification', async () => {
  for (const source of [
    'fn main() -> usize {let p: unique(usize) = alloc(42); let n = *p; drop(p); n}',
    'fn main() -> isize {linux_io::print_bytes(&"hi")}',
  ]) {
    const { metadata, module } = await compile(source);
    assert.equal(metadata.ok, false);
    assert.equal(metadata.stage, source.includes('linux_io') ? 'verify' : 'compile');
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


test('wasm32 layout and narrow arithmetic agree before and after storage', async () => {
  for (const [source, expected] of [
    ['fn main() -> usize {size_of(usize) + size_of(&usize) + size_of(u64)}', '16'],
    ['fn main() -> usize {usize::MAX + 1}', '0'],
    ['fn main() -> isize {isize::MAX + 1}', '-2147483648'],
    ['fn main() -> u8 {u8::MAX + 1}', '0'],
    ['fn main() -> i8 {i8::MAX + 1}', '-128'],
    ['fn main() -> u16 {u16::MAX + 1}', '0'],
    ['fn main() -> i16 {i16::MAX + 1}', '-32768'],
    ['fn main() -> bool {(usize::MAX + 1) == 0}', 'true'],
    ['fn main() -> bool {(i8::MAX + 1) < 0}', 'true'],
    ['fn main() -> usize {let a: [usize; 2] = [7, 42]; let p = &a; (*p)[1]}', '42'],
  ]) assert.equal((await execute(source)).result, expected, source);
});


test('zero-sized fields and arrays preserve neighboring bytes', async () => {
  const source = 'type Packed struct {first: u8, empty: unit, last: u8} fn touch(x: &unit) modifies(x) {*x = ();} fn main() -> usize {proof _: size_of(unit) == 0 && size_of(Packed) == 2; let p = Packed {first: 7, empty: (), last: 42}; touch(&p.empty); let a: [unit; 2] = [(), ()]; touch(&a[1]); if p.first == 7 && p.last == 42 {42} else {0}}';
  assert.equal((await execute(source)).result, '42');
  assert.equal((await execute('fn main() -> bool {let a: [unit; 2] = [(), ()]; &a[0] == &a[1]}')).result, 'true');
  assert.equal((await compile('fn main() {let a: [unit; 2] = [(), ()]; proof _: &a[0] != &a[1];}')).metadata.ok, false);
});
