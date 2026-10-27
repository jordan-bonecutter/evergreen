//! Native execution, layouts, cleanup ordering, and resource-budget regressions.

use super::*;
use crate::compiler::verify::verify;

#[test]
fn native_loop_termination_measures_are_erased() {
    let source = include_str!("../../../examples/while_termination.evg");
    let measured = verify(source).unwrap();
    let unmeasured = verify(
        &source
            .replace("decreases(limit - count)", "")
            .replace("proof total_contract: count_to(42) == 42;", ""),
    )
    .unwrap();
    assert_eq!(emit(&measured).unwrap(), emit(&unmeasured).unwrap());
}

#[test]
fn native_rejects_unsupported_layouts_and_entry_assumptions() {
    for source in [
        "fn read(n: usize, a: [usize; n]) -> usize {n} fn main() -> usize {0}",
        "type Dynamic struct {len: usize, data: [usize; len]} fn main() -> usize {let d = Dynamic {len: 1, data: [42]}; d.data[0]}",
        "fn main() -> usize where (false) {0}",
        "fn main() -> [usize; 1] {[0]}",
    ] {
        let program = verify(source).unwrap();
        assert!(
            emit(&program).is_err(),
            "accepted unsupported native source: {source}"
        );
    }
}

#[test]
fn native_emits_path_dependent_local_cleanup() {
    let source = "fn consume(value: shared(usize), flag: bool) where owner_count(value) == 1 {if flag {let final: unique(usize) = move(value); drop(final);} else {}} fn main() -> usize {let unique: unique(usize) = alloc(7); consume(unique, false); 42}";
    let program = verify(source).unwrap();
    assert_eq!(program.run().unwrap().to_string(), "42");
    assert!(emit(&program).is_ok());
}

#[test]
fn native_stack_bound_includes_the_call_tree() {
    let mut source = String::new();
    for index in 0..34 {
        source.push_str(&format!("fn f{index}() -> usize {{"));
        for local in 0..250 {
            source.push_str(&format!("let x{local}: usize = 0;"));
        }
        if index == 0 {
            source.push_str("42}");
        } else {
            source.push_str(&format!("f{}()}}", index - 1));
        }
    }
    source.push_str("fn main() -> usize {f33()}");
    let program = verify(&source).unwrap();
    assert!(emit(&program).unwrap_err().contains("stack budget"));
    let mut source = "fn f0(a: [usize; 512]) -> usize {a[0]}".to_string();
    for index in 1..6 {
        source.push_str(&format!(
            "fn f{index}(a: [usize; 512]) -> usize {{f{}(a)}}",
            index - 1
        ));
    }
    let values = vec!["0"; 512].join(",");
    source.push_str(&format!(
        "fn main() -> usize {{let a: [usize; 512] = [{values}]; f5(a)}}"
    ));
    let program = verify(&source).unwrap();
    assert!(emit(&program).unwrap_err().contains("stack budget"));
    let recursive = "fn recurse(n: usize) -> usize ensures(result == n) decreases(n) {let a: [usize; 128] = [VALUES]; if n == 0 {0} else {recurse(n - 1) + 1}} fn main() -> usize {recurse(1)}".replace("VALUES", &vec!["0"; 128].join(","));
    assert!(emit(&verify(&recursive).unwrap())
        .unwrap_err()
        .contains("stack budget"));
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn execute_test_binary(
    path: &std::path::Path,
    binary: &[u8],
    source: &str,
) -> std::process::ExitStatus {
    execute_test_binary_to(path, binary, source, std::process::Stdio::null())
}

fn execute_test_binary_to(
    path: &std::path::Path,
    binary: &[u8],
    source: &str,
    stdout: std::process::Stdio,
) -> std::process::ExitStatus {
    use std::{
        fs,
        os::unix::fs::PermissionsExt,
        process::{Command, Stdio},
        time::{Duration, Instant},
    };
    fs::write(path, binary).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    let mut command = Command::new(path);
    command
        .stdin(Stdio::null())
        .stdout(stdout)
        .stderr(Stdio::null());
    let deadline = Instant::now() + Duration::from_secs(3);
    let mut child = loop {
        match command.spawn() {
            Ok(child) => break child,
            // A concurrently starting child can briefly inherit a writable
            // descriptor before close-on-exec. Retry only that Linux race.
            Err(error)
                if error.kind() == std::io::ErrorKind::ExecutableFileBusy
                    && Instant::now() < deadline =>
            {
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(error) => panic!("native test could not start: {error}: {source}"),
        }
    };
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("native test timed out: {source}");
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    status
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_execution_agrees_with_the_interpreter() {
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("evergreen-native-{}-{stamp}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let mut cases = [
        include_str!("../../../examples/string_bytes.evg"),
        include_str!("../../../examples/utf8_literal.evg"),
        include_str!("../../../examples/utf8_view.evg"),
        include_str!("../../../examples/buffer_copy.evg"),
        include_str!("../../../examples/while_termination.evg"),
        include_str!("../../../examples/loop.evg"),
        include_str!("../../../examples/match.evg"),
        include_str!("../../../examples/match_blocks.evg"),
        "type Guard struct {target: &usize} impl Drop for Guard {fn drop(self) modifies(self.target) ensures *self.target == 42 {*self.target = 42;}} fn main() -> usize {let owner = {let local: unique(usize) = alloc(7); let guard = Guard {target: &*local}; local}; *owner}",
        "type Resource struct {tag: usize} impl Drop for Resource {fn drop(self) {}} fn read(a: &Resource, b: usize) -> usize where b <= 35 && a.tag == 7 {a.tag + b} fn main() -> usize {read(&{let item = Resource {tag: 7}; item}, {let value: usize = 35; value})}",
        "fn main() -> usize {let value: usize = 0; if true {let answer: usize = 42; value = answer;} value}",
        "fn main() -> usize {let owner: unique(usize) = alloc(42); let moved = match false {true => {let selected = owner; selected}, false => {let selected = owner; selected}}; *moved}",
        include_str!("../../../examples/conditional_planes.evg"),
        include_str!("../../../examples/conditional_stores.evg"),
        include_str!("../../../examples/conditional_store_order.evg"),
        "fn set(value: &usize) modifies(value) ensures *value == 42 {*value = 42;} fn work(a: &usize, b: &usize, flag: bool) modifies(a, b) {let selected = if flag {a} else {b}; set(selected);} fn main() -> usize {let value: usize = 7; work(&value, &value, false); value}",
        "fn choose(flag: &bool, a: &usize, b: &usize) -> &usize modifies(flag) borrows(a) when *flag else borrows(b) ensures *flag == !old(*flag) {let selected = *flag; *flag = !*flag; if selected {a} else {b}} fn main() -> usize {let flag = true; let a: usize = 42; let b: usize = 7; *choose(&flag, &a, &b)}",
        include_str!("../../../examples/sparse_arrays.evg"),
        include_str!("../../../examples/owning_references.evg"),
        include_str!("../../../examples/generics.evg"),
        include_str!("../../../examples/layout_queries.evg"),
        "fn main() -> usize {if size_of(Later) == 4 && align_of(shape(Later)) == 2 {42} else {1}} type Later struct {byte: u8, word: u16}",
        "fn main() -> usize {let n: usize = 7; if size_of(unique(u8, n)) == 8 {42} else {1}}",
        "type Box<T> struct {value: T} impl<T> Box<T> {fn new(value: T) -> Self {Self {value: value}} method& get() -> &T borrows(&self.value) {&self.value}} fn main() -> usize {let value = Box::<usize>::new(42); *value.get()}",
        "type Box<T> struct {value: T} impl<T> Drop for Box<T> {fn drop(self) {let Self {value} = self; drop(value);}} fn main() -> usize {let value = Box::<usize> {value: 42}; value.value}",
        "type Resource<T> struct {value: T} impl<T> Drop for Resource<T> {fn drop(self) {}} impl<T> Resource<T> {method inspect() -> usize {42}} fn main() -> usize {let value = Resource::<usize> {value: 7}; value.inspect()}",
        "type Box<T> struct {value: T} fn unpack<T>(input: Box<T>) -> T {let Box::<T> {value: payload} = input; payload} fn main() -> usize {unpack::<usize>(Box::<usize> {value: 42})}",
        "type Pair<T> struct {a: T, b: T} fn identity<T>(value: T) -> T {value} fn main() -> u8 {let pair = Pair::<u8> {a: 7, b: 42}; identity::<u8>(pair.b)}",
        "fn identity<T>(value: T) -> T {value} fn main() -> usize {let value: unique(usize) = alloc(42); let final = identity::<unique(usize)>(value); *final}",
        "type Box<T> struct {value: T} fn main() -> usize {let value: Box<unique(usize)> = Box::<unique(usize)> {value: alloc(42)}; *value.value}",
        "fn identity<T>(value: T) -> T ensures (typeof(result) == T) {value} fn main() -> usize {identity::<usize>(42)}",
        "fn main() -> usize {let first: shared(usize) = alloc(42); let items = [first, first]; let other = items; leak(other); let selected = items[0]; leak(selected); leak(items); let final: unique(usize) = move(first); *final}",
        "type Handle struct {data: shared(usize)} impl Copy for Handle {} fn main() -> usize {let first: shared(usize) = alloc(42); let original = Handle {data: first}; let other = original; leak(other); leak(original); let final: unique(usize) = move(first); *final}",
        "fn copy(value: &shared(usize)) -> shared(usize) {*value} fn main() -> usize {let first: shared(usize) = alloc(42); let view = &*copy(&first); first; let final: unique(usize) = move(first); *view}",
        "type Resource struct {value: usize} impl Drop for Resource {fn drop(self) {}} fn main() -> usize {let first: shared(Resource) = alloc(Resource {value: 42}); let second = first; leak(first); let final: unique(Resource) = move(second); final.value}",
        "fn share_owner(x: usize) -> usize {x} fn duplicate_owner(x: usize) -> usize {share_owner(x)} fn release_owner(x: usize) -> usize {duplicate_owner(x)} fn recover_owner(x: usize) -> usize {release_owner(x)} fn main() -> usize {recover_owner(42)}",
        include_str!("../../../examples/allocation_credits.evg"),
        include_str!("../../../examples/rc.evg"),
        include_str!("../../../examples/rc_generic.evg"),
        "fn prepare() -> rc::Rc<unique(u8, 1000000000)> {let data: unique(u8, 1000000000) = alloc(1000000000, 0); rc::new::<unique(u8, 1000000000)>(data)} fn main() -> usize {42}",
        "fn main() -> usize {let first = rc::new::<unique(usize)>(alloc(42)); let view = &**first.value(); let second = first.clone(); drop(first); *view}",
        "fn main() -> u8 {let first = rc::new::<[u8; 2]>([7, 42]); let view = first.value(); let second = first.clone(); drop(first); (*view)[1]}",
        "type Resource struct {tag: usize} where tag == 42; impl Drop for Resource {fn drop(self) {proof valid: self.tag == 42;}} fn main() -> usize {let inner = rc::new::<Resource>(Resource {tag: 42}); let outer = rc::new::<rc::Rc<Resource>>(inner); let second = outer.clone(); drop(outer); second.value().value().tag}",
        "fn main() -> usize {let payload: shared(usize) = alloc(42); let first = rc::new::<shared(usize)>(payload); let second = first.clone(); drop(first); drop(second); let final: unique(usize) = move(payload); *final}",
        include_str!("../../../examples/rc_drop.evg"),
        include_str!("../../../examples/conditional_rc_drop.evg"),
        include_str!("../../../examples/replacement_rhs.evg"),
        "type Resource struct {data: unique(usize), target: &usize} impl Drop for Resource {fn drop(self) modifies(self.target) {*self.target = 42;}} fn main() -> usize {let ignored: usize = 0; let replacement: unique(usize) = alloc(7); let value = Resource {data: alloc(0), target: &*replacement}; value = Resource {data: replacement, target: &ignored}; *value.data}",
        "type Resource struct {data: unique(usize)} impl Drop for Resource {fn drop(self) {}} fn main() -> usize {let value = Resource {data: alloc(7)}; let header = &value.data; value = {value = Resource {data: alloc(8)}; Resource {data: alloc(42)}}; **header}",
        "type Resource struct {data: unique(usize)} impl Drop for Resource {fn drop(self) {}} type Holder struct {value: Resource} fn main() -> usize {let holder = Holder {value: Resource {data: alloc(7)}}; holder.value = {holder.value = Resource {data: alloc(8)}; Resource {data: alloc(42)}}; *holder.value.data}",
        "fn main() -> usize {let value = rc::new(7); value = {value = rc::new(8); rc::new(42)}; *value.value()}",
        "fn consume(value: shared(usize), flag: bool) where owner_count(value) == 1 {if flag {let final: unique(usize) = move(value); drop(final);} else {}} fn main() -> usize {let unique: unique(usize) = alloc(7); consume(unique, false); 42}",
        "fn consume(value: shared(usize), flag: bool) where owner_count(value) == 1 {if flag {let final: unique(usize) = move(value); drop(final);} else {}} fn main() -> usize {let unique: unique(usize) = alloc(7); consume(unique, true); 42}",
        "fn consume(value: shared(usize), flag: bool) -> usize where owner_count(value) == 1 {let view = &*value; if flag {let final: unique(usize) = move(value); drop(final);} else {} if flag {42} else {*view}} fn main() -> usize {let unique: unique(usize) = alloc(42); consume(unique, false)}",
        "fn main() -> usize {let first = rc::new(42); let group = [first.clone(), first.clone()]; drop(group); if first.strong_count() == 1 {*first.value()} else {1}}",
        "fn replace(value: rc::Rc) -> rc::Rc where value.strong_count() < usize::MAX {let next = value.clone(); next} fn main() -> usize {let first = rc::new(42); let view = first.value(); let second = replace(first); if second.strong_count() == 1 {*view} else {1}}",
        "fn duplicate(value: &shared(usize), flag: bool) -> shared(usize) {if flag {*value} else {*value}} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = duplicate(&first, false); leak(second); *first}",
        include_str!("../../../examples/conditional_ownership.evg"),
        "fn release(value: shared(usize), flag: bool) where owner_count(value) == 1 {if flag {let unique: unique(usize) = move(value); drop(unique);} else {let unique: unique(usize) = move(value); drop(unique);}} fn main() -> usize {let unique: unique(usize) = alloc(7); let value: shared(usize) = move(unique); release(move(value), false); 42}",
        "fn main() -> usize {let items = [rc::new(42)]; let view = items[0].value(); let second = items[0].clone(); second.release_nonfinal(); *view}",
        "type Holder struct {shared: rc::Rc} fn main() -> usize {let holder = Holder {shared: rc::new(7)}; let view = holder.shared.value(); let second = holder.shared.clone(); *view = 42; second.release_nonfinal(); *holder.shared.value()}",
        "type Resource struct {value: usize} where value == 42; impl Drop for Resource {fn drop(self) {proof valid: self.value == 42;}} fn main() -> usize {let unique: unique(Resource) = alloc(Resource {value: 42}); let first: shared(Resource) = move(unique); let second = first; leak(first); second.value}",
        "fn duplicate(value: &shared(usize)) -> shared(usize) ensures owner_count(result) == old(owner_count(value)) + 1 {*value} fn main() -> usize {let unique: unique(usize) = alloc(42); let first: shared(usize) = move(unique); let second = duplicate(&first); leak(first); *second}",
        r#"fn main() -> usize {let bytes = ""; let text = utf8::Text::from_bytes(&bytes); if text.len() == 0 {42} else {1}}"#,
        r#"fn main() -> usize {let bytes = "a"; let text = utf8::Text::from_bytes(&bytes); bytes[0] = 98; if text.byte(0) == 98 {42} else {1}}"#,
        "type Resource struct {value: usize} fn consume(value: Resource) -> usize {value.value} impl Drop for Resource {fn drop(self) {mark(self.value);}} fn mark(value: usize) {} fn main() -> usize {consume(Resource {value: 42})}",
        "fn needs_bound(n: usize) -> usize where n < usize::MAX {n + 1} type Coupled struct {left: &usize, right: &usize} where left == right; impl Drop for Coupled {fn drop(self) {let next = needs_bound(*self.left);}} fn main() -> usize {let value: usize = 41; let coupled = Coupled {left: &value, right: &value}; 42}",
        r#"fn consume(value: [u8; 0]) -> usize {42} fn main() -> usize {let value: [u8; 0] | bool = ""; consume(move(value))}"#,
        include_str!("../../../examples/raw_union.evg"),
        include_str!("../../../examples/raw_union_drop.evg"),
        include_str!("../../../examples/raw_union_owner.evg"),
        include_str!("../../../examples/raw_union_borrow.evg"),
        include_str!("../../../examples/raw_union_owner_paths.evg"),
        include_str!("../../../examples/raw_union_owner_drop.evg"),
        "fn read(v: &(unique(u8) | bool)) -> u8 where typeof(*v) == unique(u8) {**v} fn dispose(v: unique(u8)) {} fn main() -> u8 {let p: unique(u8) = alloc(42); let v: unique(u8) | bool = p; let n = read(&v); dispose(v); n}",
        "fn view(value: &(usize | bool)) -> usize where typeof(*value) == usize {*value} fn main() -> usize {let value: usize | bool = 42; let n = view(&value); let consumed: usize = value; n}",
        "fn first(value: [u8; 2]) -> u8 {value[0]} fn main() -> u8 {let payload: [u8; 2] | bool = [42, 7]; first(payload)}",
        "fn extract(value: i8 | usize) -> i8 where typeof(value) == i8 {let n: i8 = value; n} fn main() -> usize {if extract(i8(-42)) == -42 {42} else {1}}",
        "type NonZero struct {data: usize} where data != 0; fn read(value: NonZero | usize) -> usize where (typeof(value) == NonZero) {let n: NonZero = value; n.data - 1} fn main() -> usize {read(NonZero {data: 43})}",
        "fn extract(value: usize | bool) -> usize where typeof(value) == usize {let n: usize = value; n} fn main() -> usize {extract(42)}",
        "fn word(n: usize) -> usize {n} fn flag(b: bool) -> usize {if b {42} else {1}} fn choose(small: bool) -> usize {let value: usize | bool = if small {true} else {42}; if small {flag(value)} else {word(value)}} fn main() -> usize {choose(false)}",
        include_str!("../../../examples/while.evg"),
        "fn main() -> usize {let i: usize = 0; while i < 1024 invariant(i <= 1024) modifies(&i) {i = i + 1;} i - 982}",
        "fn main() -> usize {let i: usize = 0; let sum: usize = 0; while i < 3 invariant(i <= 3 && integer(sum) == 14 * integer(i)) modifies(&i, &sum) {let j: usize = 0; while j < 14 invariant(j <= 14) modifies(&j) {j = j + 1;} sum = sum + j; i = i + 1;} sum}",
        "fn fill(data: &[usize; 3]) modifies(data) {let i: usize = 0; while i < 3 invariant(i <= 3) modifies(&i, data) {let value: usize = 42; (*data)[i] = value; i = i + 1;}} fn main() -> usize {let data: [usize; 3] = [0, 0, 0]; fill(&data); data[2]}",
        "type Guard struct {target: &usize} impl Drop for Guard {fn drop(self) modifies(self.target) ensures *self.target == 42 {*self.target = 42;}} fn main() -> usize {let i: usize = 0; let out: usize = 0; while i < 2 invariant(i <= 2 && (i == 0 || out == 42)) modifies(&i, &out) {let guard = Guard {target: &out}; i = i + 1;} out}",
        include_str!("../../../examples/owned_method_transfer.evg"),
        include_str!("../../../examples/methods.evg"),
        include_str!("../../../examples/anonymous_proofs.evg"),
        include_str!("../../../examples/borrowed_fields.evg"),
        include_str!("../../../examples/nonzero.evg"),
        "fn first(length: usize, data: linear_plane(usize, length)) -> usize where length > 0 {(*data)[0]} fn forward(n: usize, data: linear_plane(usize, n)) -> usize where n > 0 {first(data)} fn main() -> usize {let data: array(usize, 2) = [42, 7]; forward(&data)}",
        include_str!("../../../examples/update_methods.evg"),
        include_str!("../../../examples/temporary_methods.evg"),
        "type Point struct {value: usize} impl Point {method& read() -> usize {self.value}} fn choose(flag: bool) -> usize {(if flag {Point {value: 7}} else {Point {value: 42}}).read()} fn main() -> usize {choose(false)}",
        "type Point struct {value: usize} impl Point {method& read() -> usize {self.value}} fn make(count: &usize) -> Point where(*count < usize::MAX) modifies(count) ensures(*count == old(*count) + 1 && result.value == 42) {*count = *count + 1; Point {value: 42}} fn main() -> usize {let count: usize = 0; let value = make(&count).read(); if count == 1 {value} else {0}}",
        "type Point struct {value: usize} impl Copy for Point {} impl Point {method read() -> usize ensures(result == self.value) {self.value}} fn main() -> usize {let p = Point {value: 21}; let reference = &p; reference.read() + p.read()}",
        "type Item struct {value: usize} impl Item {method& view() -> &usize borrows(&self.value) {&self.value}} fn main() -> usize {let item = alloc(Item {value: 42}); *item.view()}",
        "type Resource struct {done: &bool} impl Drop for Resource {method drop() modifies(self.done) ensures(*self.done) {*self.done = true;}} impl Resource {method consume() -> usize modifies(self.done) ensures(result == 42 && *self.done) {42}} fn main() -> usize {let done = false; let resource = Resource {done: &done}; let value = resource.consume(); if done {value} else {0}}",
        "type Item struct {value: usize} impl Item {method consume() -> usize {self.value}} fn make(count: &usize) -> Item where(*count < usize::MAX) modifies(count) ensures(*count == old(*count) + 1 && result.value == 42) {*count = *count + 1; Item {value: 42}} fn main() -> usize {let count: usize = 0; let value = make(&count).consume(); if count == 1 {value} else {0}}",
        include_str!("../../../examples/copy_and_move.evg"),
        include_str!("../../../examples/drop_receiver_pattern.evg"),
        include_str!("../../../examples/scalar_types.evg"),
        include_str!("../../../examples/field_access.evg"),
        "type Item struct {value: usize} fn choose(count: &usize, item: &Item) -> &Item where(*count < usize::MAX) modifies(count) borrows(item) ensures(*count == old(*count) + 1) {*count = *count + 1; item} fn main() -> usize {let n: usize = 0; let item = Item {value: 42}; let chosen = choose(&n, &item).value; if n == 1 {chosen} else {0}}",
        "type Size struct {len: usize} fn first(size: &Size, data: linear_plane(usize, size.len)) -> usize where(size.len > 0) {(*data)[0]} fn main() -> usize {let size = Size {len: 1}; let data: array(usize, 1) = [42]; first(&size, &data)}",
        "type Inner struct {value: usize} type Outer struct {inner: unique(Inner)} fn main() -> usize {let outer = alloc(Outer {inner: alloc(Inner {value: 41})}); let a = &outer; let b = &a; b.inner.value = 42; b.inner.value}",
        include_str!("../../../examples/vec.evg"),
        crate::compiler::verify::replacement_tests::OLD_SLOT_DURING_DROP,
        "fn main() -> usize {let values = vec::Vec::new(0); let header = &values; values = values.reallocate(4); proof grown: header.capacity() == 4; values.push(42); values = values.reallocate(8); proof grown_again: header.capacity() == 8; values.pop()}",
        "fn main() -> usize {let values = vec::Vec::new(1); values.push(42); let removed = values.pop(); values = values.reallocate(0); values = values.reallocate(0); proof empty: values.capacity() == 0; removed}",
        "fn main() -> usize {let a: unique(usize, 9000) = alloc(9000, 42); (*a)[8999]}",
        "fn main() -> usize {let v = vec::new(9000); vec::push(&v, 42); vec::pop(&v)}",
        "fn consume(owner: unique(usize, count), count: usize) -> usize where(count > 0) {(*owner)[0]} fn main() -> usize {let count: usize = 7; let owner: unique(usize, 2) = alloc(2, 42); consume(owner, 2)}",
        "fn main() -> usize {let v = vec::new(0); v = vec::reallocate(&v, 2); vec::push(&v, 42); let p = vec::get(&v, 0); vec::push(&v, 7); *p}",
        include_str!("../../../examples/runtime_planes.evg"),
        "fn main() -> usize {let a: unique(usize, 0) = alloc(0, 7); let b: unique(usize, 0) = alloc(0, 9); if &*a != &*b {42} else {1}}",
        "fn first(n: usize, data: linear_plane(u8, n), fixed: array(u16, 2)) -> u8 where(n > 0) {(*data)[0]} fn main() -> u8 {let data: array(u8, 1) = [42]; first(1, &data, [7, 9])}",
        "fn make(n: usize) -> unique(u8, n) where(n > 0 && n <= 65536) {alloc(n, 255)} fn main() -> usize {let data = make(7); if (*data)[0] == 255 && (*data)[6] == 255 {42} else {1}}",
        "fn main() -> usize {let data: unique(i8, 3) = alloc(3, -128); (*data)[1] = -42; if (*data)[0] == -128 && (*data)[1] == -42 && (*data)[2] == -128 {42} else {1}}",
        "type Pair struct {a: u8, b: u16, c: bool} impl Copy for Pair {} fn main() -> usize {let data: unique(Pair, 3) = alloc(3, Pair {a: 255, b: 65535, c: true}); (*data)[1].b = 42; if (*data)[0].b == 65535 && (*data)[1].a == 255 && (*data)[1].b == 42 && (*data)[2].c {42} else {1}}",
        "fn tick(n: &usize) -> usize where(*n < usize::MAX) modifies(n) ensures(*n == old(*n) + 1 && result == 7) {*n = *n + 1; 7} fn main() -> usize {let n: usize = 3; let before = n; let data: unique(usize, before) = alloc(n, tick(&n)); if n == 4 && (*data)[2] == 7 {42} else {1}}",
        "fn sum(ideal n: nat, a: &[u8; n], ideal m: nat, b: &[u8; m]) -> u16 where(n > 0 && m > 0) {u16((*a)[0]) + u16((*b)[0])} fn main() -> u16 {let a: [u8; 1] = [40]; let b: [u8; 2] = [2, 3]; sum(&a, &b)}",
        "fn main() -> usize {let data: [usize; 2] = [7, 1]; arrays::set(&data, 1, 42); data[1]}",
        include_str!("../../../examples/owned_return_cleanup.evg"),
        include_str!("../../../examples/owned_destructor_cleanup.evg"),
        include_str!("../../../examples/integer_conversions.evg"),
        "fn main() -> usize {let small: i32 = i32::MIN; let wide = i64(small); let positive = u64(u32::MAX); if wide == -2147483648 && positive == 4294967295 {42} else {1}}",
        "fn widen(n: u8) -> usize ensures(nat(result) == nat(n)) {usize(n)} type Resource struct {tag: u8} where(tag == 7); impl Drop for Resource {fn drop(self) {let tag = widen(self.tag); proof valid: tag == 7;}} fn change(n: &u8) where(*n < u8::MAX) modifies(n) ensures(usize(*n) == old(usize(*n)) + 1) {*n = *n + 1;} fn main() -> usize {let resource = Resource {tag: 7}; let n: u8 = 41; change(&n); widen(n)}",
        "fn first(bytes: &[u8; length], length: usize) -> u8 where(length > 0) {(*bytes)[0]} fn change(length: &usize) -> usize modifies(length) ensures(result == 2 && *length == 2) {*length = 2; 2} fn main() -> u8 {let length: usize = 1; let bytes: [u8; 2] = [42, 7]; let byte = first(&bytes, change(&length)); if byte == 42 && length == 2 {42} else {1}}",
        include_str!("../../../examples/native_layouts.evg"),
        "type Tiny struct {data: [u8; 3]} impl Drop for Tiny {fn drop(self) {}} fn forward(value: Tiny) -> Tiny {value} fn main() -> u8 {let item = forward(Tiny {data: [1, 2, 42]}); item.data[2]}",
        "fn main() -> u8 {let data: [[u64; 0]; 2] = [[], []]; if &data[0] != &data[1] {42} else {1}}",
        "fn forward(a: [u8; 7], marker: u8) -> [u8; 7] {a} fn main() -> u8 {let a: [u8; 7] = [1, 2, 3, 4, 5, 6, 42]; let b = forward(a, 99); b[6]}",
        "type Mixed struct {a: u8, b: u32, c: i16, flag: bool} fn forward(x: Mixed, n: u8) -> Mixed {x} fn main() -> i16 {let x = Mixed {a: 255, b: 4294967295, c: -42, flag: true}; let y = forward(x, 7); if y.a == 255 && y.b == 4294967295 && y.c == -42 && y.flag {42} else {1}}",
        "fn forward(a: [u8; 3], b: i8, c: [u16; 3], d: i32) -> i32 {d} fn main() -> i32 {forward([1, 2, 3], -128, [4, 5, 65535], -42)}",
        "fn main() -> u8 {let a: [u8; 3] = [1, 2, 3]; let middle = &a[1]; *middle = 42; if a[0] == 1 && a[1] == 42 && a[2] == 3 {42} else {1}}",
        "type Small struct {left: u8, value: u16, right: u8} fn main() -> u8 {let a = Small {left: 7, value: 65535, right: 9}; a.value = 0; a.left + a.right}",
        "fn main() -> i8 {let n: i8 = -42; let q = alloc(n); if *q == -42 {42} else {1}}",
        include_str!("../../../examples/partial_recursion.evg"),
        include_str!("../../../examples/ideal_bindings.evg"),
        "type Resource struct {tag: usize} where(tag == 42); impl Drop for Resource {fn drop(self){}} ideal fn observe(r: &Resource) -> nat ensures(result == nat((*r).tag)) {nat((*r).tag)} fn main() -> usize {let r = Resource {tag: 42}; ideal let saved = observe(&r); proof correct: saved == 42; r.tag}",
        include_str!("../../../examples/erased_resources.evg"),
        "fn answer(ideal expected: nat) -> usize where(expected == 42) ensures(result == 42) {42} fn caller(n: usize) -> usize where(n == 42) ensures(result == 42) {n = 0; answer(nat(old(n)))} fn main() -> usize {caller(42)}",
        "fn answer(ideal data: [usize; 1]) -> usize where(data[0] == 42) ensures(result == 42) {42} fn main() -> usize {answer([42])}",
        include_str!("../../../examples/opaque_values.evg"),
        "module a {fn get() -> usize ensures(result == 20) {20}} module b {fn get() -> usize ensures(result == 22) {22}} fn main() -> usize {a::get() + b::get()}",
        "module owned {opaque type Resource struct {tag: usize} where(self.tag == 42); impl Drop for Resource {fn drop(self) {proof valid: self.tag == 42;}} fn make() -> Resource {Resource {tag: 42}} fn read(r: &Resource) -> usize ensures(result == (*r).tag) {(*r).tag}} fn main() -> usize {let r = owned::make(); owned::read(&r)}",
        include_str!("../../../examples/indexed_borrows.evg"),
        include_str!("../../../examples/weak_invariant.evg"),
        "fn main() -> bool {false => true => false}",
        "fn main() -> bool {true => false}",
        include_str!("../../../examples/array_borrows.evg"),
        include_str!("../../../examples/borrow_returns.evg"),
        include_str!("../../../examples/computed_places.evg"),
        include_str!("../../../examples/old_places.evg"),
        include_str!("../../../examples/reference_fields.evg"),
        include_str!("../../../examples/drop_effects.evg"),
        include_str!("../../../examples/drop_children.evg"),
        include_str!("../../../examples/owned_borrows.evg"),
        include_str!("../../../examples/owned_planes.evg"),
        include_str!("../../../examples/owned_result_views.evg"),
        include_str!("../../../examples/heap_updates.evg"),
        "fn main() -> usize {let p: unique(usize) = alloc(42); *p}",
        "fn forward(p: unique(usize)) -> unique(usize) {p} fn main() -> usize {let p = forward(alloc(42)); *p}",
        "type Owner struct {data: unique([usize; 2])} fn main() -> usize {let owner = Owner {data: alloc([7, 42])}; (*owner.data)[1]}",
        "fn main() -> usize {let p: unique(usize) = alloc(1); drop(p); p = alloc(42); *p}",
        "fn main() -> isize {*alloc(42)}",
        "type Resource struct {n: usize} impl Drop for Resource {fn drop(self){}} fn main() -> usize {(*alloc(Resource {n: 42})).n}",
        "fn main() -> usize {let p: unique([usize; 2]) = alloc([7, 42]); (*p)[1]}",
        "fn main() -> usize {let p: unique(unique(usize)) = alloc(alloc(42)); **p}",
        "fn main() -> usize {let p: unique([unique(usize); 2]) = alloc([alloc(7), alloc(42)]); *(*p)[1]}",
        "fn main() -> usize {let p: unique(usize) = alloc(41); let view = &*p; let nested = alloc(p); *view = 42; *view}",
        "type Holder struct {owner: unique(usize)} fn main() -> usize {let p: unique(usize) = alloc(42); let view = &*p; let h = Holder {owner: p}; let Holder {owner: q} = h; *view}",
        "type Child struct {n: usize} impl Drop for Child {fn drop(self){}} type Parent struct {child: unique(Child)} impl Drop for Parent {fn drop(self){}} fn main() -> usize {let p = alloc(Parent {child: alloc(Child {n: 42})}); (*(*p).child).n}",
        "type Empty struct {} fn main() -> usize {let a = alloc(Empty {}); let b = alloc(Empty {}); if &*a != &*b {42} else {0}}",
        include_str!("../../../examples/borrowed_view.evg"),
        include_str!("../../../examples/borrowed_array.evg"),
        include_str!("../../../examples/borrowed_array_owners.evg"),
        include_str!("../../../examples/reference_array_inputs.evg"),
        include_str!("../../../examples/aliasing_calls.evg"),
        include_str!("../../../examples/propositional_proofs.evg"),
        include_str!("../../../examples/proof_cases.evg"),
        include_str!("../../../examples/reference_identity.evg"),
        include_str!("../../../examples/conditional_borrows.evg"),
        "fn choose(flag: bool) -> [usize; 2] ensures((flag => result[0] == 42) && (!flag => result[1] == 42)) {if flag {[42, 7]} else {[7, 42]}} fn main() -> usize ensures(result == 42) {let data = choose(false); data[1]}",
        include_str!("../../../examples/conditional_drop.evg"),
        include_str!("../../../examples/conditional_contracts.evg"),
        include_str!("../../../examples/old_selection.evg"),
        include_str!("../../../examples/old_accessors.evg"),
        include_str!("../../../examples/array_frame_history.evg"),
        include_str!("../../../examples/array_branch_history.evg"),
        include_str!("../../../examples/array_model.evg"),
        include_str!("../../../examples/record_array_history.evg"),
        include_str!("../../../examples/record_array_values.evg"),
        include_str!("../../../examples/record_array_borrows.evg"),
        include_str!("../../../examples/update_calls.evg"),
        include_str!("../../../examples/self_observing_fields.evg"),
        include_str!("../../../examples/update_borrow_writes.evg"),
        include_str!("../../../examples/ideal_borrow_resources.evg"),
        include_str!("../../../examples/ideal_update_state.evg"),
        include_str!("../../../examples/ideal_fields.evg"),
        include_str!("../../../examples/ideal_borrow_writes.evg"),
        "fn main() -> usize where(old(1 + 1) == 2) {42}",
        "type Fixed struct {value: usize} where(value == 42); fn refresh(r: &Fixed) -> &Fixed modifies(&(*r).value) borrows(r) ensures((*r).value == 42 && (*result).value == 42) {(*r).value = 42; r} fn main() -> usize {let fixed = Fixed {value: 42}; let refreshed = refresh(&fixed); (*refreshed).value}",
        include_str!("../../../examples/recursion.evg"),
        include_str!("../../../examples/drop.evg"),
        include_str!("../../../examples/temporary_cleanup.evg"),
        include_str!("../../../examples/borrowed_temporaries.evg"),
        include_str!("../../../examples/native.evg"),
        include_str!("../../../examples/native_aggregates.evg"),
        include_str!("../../../examples/array_contracts.evg"),
        include_str!("../../../examples/destructure.evg"),
        include_str!("../../../examples/move_values.evg"),
        include_str!("../../../examples/structs.evg"),
        include_str!("../../../examples/conditional_records.evg"),
        "fn identity(a: [usize; 2]) -> [usize; 1 + 1] {a} fn main() -> usize {let input: [usize; 2] = [7, 42]; let a: [usize; 2] = identity(input); a[1]}",
        "fn empty() -> [usize; 0] {[]} fn main() -> usize {let a = empty(); 42}",
        "type Pair struct {left: usize, right: usize} impl Copy for Pair {} fn pick(p: Pair, marker: usize) -> usize ensures (result == p.left) {p.left} fn set(r: &usize) -> usize modifies(r) ensures (*r == 99 && result == 0) {*r = 99; 0} fn main() -> usize ensures (result == 42) {let p = Pair {left: 42, right: 0}; pick(p, set(&p.left))}",
        include_str!("../../../examples/intermediate_states.evg"),
        include_str!("../../../examples/conditional_writes.evg"),
        "fn head(ideal n: nat, data: &[usize; n]) -> usize where (n > 0) {(*data)[0]} fn main() -> usize {let a: [usize; 1] = [42]; head(1, &a)}",
        "fn set(r: &usize) -> usize modifies(r) ensures (*r == 99 && result == 0) {*r = 99; 0} fn main() -> usize {let a: [usize; 1] = [42]; a[set(&a[0])]}",
        "type Values struct {first: usize, second: usize} fn set(r: &usize) -> usize modifies(r) ensures (*r == 99 && result == 0) {*r = 99; 0} fn main() -> usize {let n: usize = 42; let v = Values {first: n, second: set(&n)}; v.first}",
        "fn main() -> usize {let a: [usize; (1 - 2) + 2] = [7, 42]; a[1]}",
        "fn main() -> usize {let a: [[usize; 2]; 2] = [[1, 2], [3, 42]]; a[1][1]}",
        "fn main() -> i8 {-128}",
        "fn main() -> u8 {255}",
        "fn main() -> u64 {u64::MAX}",
        "fn main() -> i64 {i64::MIN}",
        "fn main() -> bool {let x: i64 = -1; x < 0}",
        "fn main() -> bool {let x: u64 = u64::MAX; x > 0}",
        "fn main() -> bool {(1 < 2) == !(3 < 2)}",
        "fn main() -> usize {let x: usize = 42; let y = move(x); y}",
        "fn main() -> usize {let x: usize = 1; drop(x); x = 42; x}",
        "fn main() -> usize {let x: usize = 1; let r = &x; *r = 42; x}",
        "fn main() -> usize {let x: usize = 1; let a = &x; let b = &x; *a = 42; *b}",
        "fn main() -> usize {let x: usize = 42; let r = &x; let rr = &r; **rr}",
        "fn main() -> usize {let x: usize = 1; let y: usize = 42; let r = &x; let rr = &r; r = &y; **rr}",
        "fn read(r: &usize) -> usize ensures (result == *r) {*r} fn main() -> usize {let x: usize = 42; read(&x)}",
        "fn flip(r: &bool) modifies(r) ensures (*r == !old(*r)) {*r = !*r;} fn main() -> bool {let x = false; flip(&x); x}",
        "fn main() -> usize {(9 - 2) * 6}",
        "fn main() -> bool {true && (false || true)}",
        "fn main() -> () {()}",
        "type Resource struct {tag: usize} where(tag == 7); impl Drop for Resource {fn drop(self){}} fn consume(r: Resource) -> usize ensures(result == 7) {r.tag} fn recurse(n: usize, r: Resource) -> usize ensures(result == 7) decreases(n) {if n == 0 {consume(r)} else {recurse(n - 1, r)}} fn main() -> usize {let r = Resource {tag: 7}; recurse(5, r)}",
        "fn choose(a: usize, b: usize, flag: bool) -> usize ensures ((flag && result == a) || (!flag && result == b)) {if flag {a} else {b}} fn main() -> usize {choose(7, 42, false)}",
        "fn add(a: usize, b: usize) -> usize where (a <= 10 && b <= 10) ensures (result == a + b) {a + b} fn main() -> usize {add(1, add(2, 3))}",
        "fn sum(a: usize,b: usize,c: usize,d: usize,e: usize,f: usize,g: usize,h: usize) -> usize where (a <= 10 && b <= 10 && c <= 10 && d <= 10 && e <= 10 && f <= 10 && g <= 10 && h <= 10) {a+b+c+d+e+f+g+h} fn main() -> usize {sum(1,2,3,4,5,6,7,8)}",
    ].map(str::to_owned).to_vec();
    cases.push(
        include_str!("../../../examples/raw_union_owner_drop.evg").replace(
            "if present {discard_owner(data)} else {discard_empty(data)}",
            "match present {true => discard_owner(data), false => discard_empty(data)}",
        ),
    );
    cases.push(
        include_str!("../../../examples/drop_receiver_pattern.evg").replace(
            "drop(resource);",
            "let Resource {data, child} = resource; drop(child);",
        ),
    );
    cases.push(
        include_str!("../../../examples/drop_receiver_pattern.evg").replace(
            "proof local_owner_is_valid: *data == 42;",
            "proof local_owner_is_valid: *data == 42; let moved = data; drop(child); drop(moved);",
        ),
    );
    cases.push(
        [
            concat!(include_str!("../../../stdlib/arrays/array.evg"), "\u{1e}"),
            include_str!("../../../examples/array_updates.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            concat!(include_str!("../../../stdlib/arrays/array.evg"), "\u{1e}"),
            include_str!("../../../examples/write_borrows.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            include_str!("../../../stdlib/swap.evg"),
            include_str!("../../../examples/disjoint_writes.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            include_str!("../../../stdlib/counter.evg"),
            include_str!("../../../examples/counter.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            include_str!("../../../stdlib/counter.evg"),
            include_str!("../../../examples/drop_helpers.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            include_str!("../../../stdlib/counter.evg"),
            include_str!("../../../examples/drop_count.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            include_str!("../../../proofs/rc_protocol.evg"),
            include_str!("../../../stdlib/counter.evg"),
            include_str!("../../../proofs/rc_count_refinement.evg"),
            include_str!("../../../examples/rc_count.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            include_str!("../../../stdlib/counter.evg"),
            include_str!("../../../proofs/count_handles.evg"),
            include_str!("../../../examples/clone_count.evg"),
        ]
        .join("\n"),
    );
    cases.push(
        [
            include_str!("../../../stdlib/counter.evg"),
            include_str!("../../../proofs/count_handles.evg"),
            include_str!("../../../examples/batch_count.evg"),
        ]
        .join("\n"),
    );
    let deferred = include_str!("../../../examples/drop_effects.evg")
        .split("fn main")
        .next()
        .unwrap();
    for body in [
        "let count: usize = 0; StoreOnDrop {target: &count, value: 42}; count",
        "let count: usize = 0; let saved = StoreOnDrop {target: &count, value: 42}.value; count",
        "let count: usize = 0; let guard = StoreOnDrop {target: &count, value: 7}; guard = StoreOnDrop {target: &count, value: 42}; drop(guard); count",
        "let count: usize = 0; let guards: [StoreOnDrop; 2] = [StoreOnDrop {target: &count, value: 7}, StoreOnDrop {target: &count, value: 42}]; drop(guards); count",
        "let count: usize = 0; let sum = StoreOnDrop {target: &count, value: 7}.value + StoreOnDrop {target: &count, value: 42}.value; count",
    ] {
        cases.push(format!("{deferred} fn main() -> usize {{{body}}}"));
    }
    cases.push(format!("{deferred} fn array_scope(target: &usize) modifies(target) ensures(*target == 42) {{let guards: [StoreOnDrop; 2] = [StoreOnDrop {{target: target, value: 7}}, StoreOnDrop {{target: target, value: 42}}];}} fn main() -> usize {{let count: usize = 0; array_scope(&count); count}}"));
    for flag in [true, false] {
        cases.push(format!("{deferred} fn choose(target: &usize, flag: bool) -> usize modifies(target) ensures(result == *target) {{if flag {{StoreOnDrop {{target: target, value: 7}}.value}} else {{StoreOnDrop {{target: target, value: 42}}.value}}}} fn main() -> usize {{let count: usize = 0; choose(&count, {flag})}}"));
    }
    // A factory exists only in this test fixture; the shipped credit API
    // intentionally has no public minting operation.
    let credit_test = concat!(include_str!("../../../stdlib/credits/credits.evg"), "\u{1e}").replace(
        "module credits;",
        "module credits;ideal fn issue() -> Credit ensures(result.units == 42) {Credit {units: 42}}",
    );
    cases.push(format!("{credit_test} {} fn main() -> usize {{ideal let restored = transfer_existing(credits::issue()); proof conserved: credits::units(&restored) == 42; 42}}", include_str!("../../../proofs/borrowed_credit_transfer.evg")));
    cases.push(format!(
        "{credit_test} {} fn main() -> usize {{use_budget(credits::issue(), 42)}}",
        include_str!("../../../proofs/ideal_credit_bindings.evg")
    ));
    cases.push(format!("{credit_test} {} {} fn main() -> usize {{let data: usize = 42; use_borrow_budget(credits::issue(), &data)}}",
        concat!(include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"), "\u{1e}"), include_str!("../../../proofs/borrow_credits.evg")));
    cases.push(format!("{credit_test} {} {} fn main() -> usize {{let data: usize = 42; use_borrow_transfer(credits::issue(), &data)}}",
        concat!(include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"), "\u{1e}"), include_str!("../../../proofs/borrowed_token_transfer.evg")));
    let updates = format!(
        "{credit_test} {} {}",
        concat!(
            include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"),
            "\u{1e}"
        ),
        include_str!("../../../proofs/borrow_credit_updates.evg")
    );
    cases.push(format!("{updates} fn main() -> usize {{let count: usize = 42; release_budget(credits::issue(), &count) + 1}}"));
    cases.push(format!("{updates} fn main() -> usize {{ideal let parts = credits::split(credits::issue(), 1); ideal let credits::Split {{left, right}} = parts; let count: usize = 1; release_budget(left, &count) + 42}}"));
    cases.push(format!("{credit_test} {} {} fn main() -> usize {{let data: usize = 42; let carrier = carry(credits::issue(), &data); let observed = read_carrier(&carrier); consume_carrier(carrier) + observed - 42}}",
        concat!(include_str!("../../../stdlib/borrow_credits/borrow_credits.evg"), "\u{1e}"), include_str!("../../../proofs/carried_borrow_credits.evg")));
    for (ty, first, last) in [
        ("u8", "255", "42"),
        ("i8", "-128", "-42"),
        ("u16", "65535", "42"),
        ("i16", "-32768", "-42"),
        ("u32", "4294967295", "42"),
        ("i32", "-2147483648", "-42"),
        ("u64", "18446744073709551615", "42"),
        ("i64", "-9223372036854775808", "-42"),
    ] {
        cases.push(format!("fn forward(a: [{ty}; 3], b: {ty}) -> [{ty}; 3] {{a}} fn main() -> u8 {{let original: [{ty}; 3] = [{first}, 0, {last}]; let a = forward(original, {first}); let middle = &a[1]; *middle = {first}; if a[0] == {first} && a[1] == {first} && a[2] == {last} {{42}} else {{1}}}}"));
    }
    let atomic = concat!(
        include_str!("../../../stdlib/x86_64_atomics/x86_64_atomics.evg"),
        "\u{1e}"
    );
    cases.push(format!(
        "{atomic} {} {}",
        concat!(
            include_str!("../../../stdlib/atomic_counter/atomic_counter.evg"),
            "\u{1e}"
        ),
        include_str!("../../../examples/atomic_counter.evg")
    ));
    cases.push(format!(
        "{atomic} {}",
        include_str!("../../../examples/compare_exchange.evg")
    ));
    cases.push(format!("{atomic} fn main() -> usize {{let data: [usize; 2] = [7, usize::MAX]; let old = x86_64_atomics::compare_exchange(&data[1], usize::MAX, 42); if old == usize::MAX && data[0] == 7 && data[1] == 42 {{42}} else {{1}}}}"));
    cases.push(format!("{atomic} fn main() -> usize {{let owner: unique(usize) = alloc(7); let old = x86_64_atomics::compare_exchange(&*owner, 7, 42); if old == 7 {{*owner}} else {{1}}}}"));
    cases.push("extern compare_exchange64 fn cas(value: &isize, expected: isize, desired: isize) -> isize modifies(value); proof {trustme} fn main() -> usize {let value: isize = isize::MIN; let old = cas(&value, isize::MIN, -42); if old == isize::MIN && value == -42 {42} else {1}}".into());
    let indexed = include_str!("../../../examples/indexed_borrows.evg")
        .split("fn main")
        .next()
        .unwrap();
    for i in 0..2 {
        for j in 0..2 {
            cases.push(format!(
                "{indexed} fn main() -> usize {{may_alias([7, 1], {i}, {j})}}"
            ));
        }
    }
    let swap = include_str!("../../../stdlib/swap.evg");
    cases.push(format!("{swap} fn change(data: [usize; 2], i: usize, j: usize) -> usize where(i < 2 && j < 2 && i != j) ensures(result == data[j]) {{swap_usize(&data[i], &data[j]); data[i]}} fn main() -> usize {{change([7, 42], 0, 1)}}"));
    cases.push("fn signed(data: &[usize; 2], index: isize) -> &usize where(index >= 0 && index < 2) borrows(&(*data)[index]) {&(*data)[index]} fn main() -> usize {let a: [usize; 2] = [7, 42]; *signed(&a, 1)}".into());
    cases.push("fn change(data: [bool; 2], i: usize, j: usize) -> bool where(i < 2 && j < 2) ensures(i == j => result) {let a = &data[i]; let b = &data[j]; *a = true; *b} fn main() -> bool {change([false, false], 0, 0)}".into());
    let declarations = "type Resource struct {tag: usize} where (tag == 7); impl Drop for Resource {fn drop(self){}} fn make() -> Resource {Resource {tag: 7}} fn consume(r: Resource) -> usize {r.tag}";
    cases.push(
        include_str!("../../../examples/replacement_rhs.evg")
            .replace("    value = {", "    drop(value);\n    value = {"),
    );
    for choice in ["false", "true"] {
        for body in [
            "if flag {drop(r);} else {} 42",
            "if flag {consume(r);} else {} 42",
            "if flag {drop(r);} else {} r = make(); r.tag",
            "r = if flag {r} else {make()}; r.tag",
            "r = if flag {let moved = r; moved} else {let fresh = make(); fresh}; r.tag",
            "{let local = make(); if flag {drop(local);} else {}}; {let local = make(); if flag {} else {drop(local);}}; 42",
        ] {
            cases.push(format!("{declarations} fn act(r: Resource, flag: bool) -> usize {{{body}}} fn main() -> usize {{act(make(), {choice})}}"));
        }
        cases.push(format!("{declarations} fn act(r: unique(Resource), flag: bool) -> usize {{if flag {{drop(r);}} else {{}} 42}} fn main() -> usize {{act(alloc(make()), {choice})}}"));
        cases.push(format!("{declarations} fn act(r: [Resource; 2], flag: bool) -> usize {{if flag {{drop(r);}} else {{}} 42}} fn main() -> usize {{act([make(), make()], {choice})}}"));
        cases.push(format!("type Left struct {{}} impl Drop for Left {{fn drop(self) {{}}}} type Right struct {{}} impl Drop for Right {{fn drop(self) {{}}}} fn act(left: Left, right: Right, flag: bool) {{if flag {{drop(left);}} else {{drop(right);}}}} fn main() -> usize {{act(Left {{}}, Right {{}}, {choice}); 42}}"));
    }
    cases.push(format!("{declarations} fn main() -> usize {{let i: usize = 0; while i < 3 invariant i <= 3 modifies(&i) decreases(3 - i) {{let local = make(); if i == 1 {{drop(local);}} else {{}} i = i + 1;}} 42}}"));
    for body in [
        "let r = make(); let s = r; s.tag",
        "let r = make(); r = make(); r.tag",
        "let r = make(); r = move(r); r.tag",
        "Resource {tag: 7}; 7",
        "make().tag",
        "let r = make(); let s = if true {move(r)} else {move(r)}; s.tag",
        "let r = make(); if true {move(r)} else {move(r)}; 7",
        "let r = make(); drop(r); 7",
        "let r = make(); consume(r)",
        "[Resource {tag: 7}]; 7",
        "let a: [Resource; 2] = [make(), make()]; a[0].tag",
        "let a: [Resource; 0] = []; 7",
    ] {
        cases.push(format!("{declarations} fn main() -> usize {{{body}}}"));
    }
    cases.extend(
        crate::compiler::verify::array_model::concrete_cases()
            .into_iter()
            .chain(crate::compiler::verify::array_model::record_cases())
            .map(|(source, _)| source),
    );
    let pair = "type Left struct {} impl Drop for Left {fn drop(self){}} type Right struct {} impl Drop for Right {fn drop(self){}} type Pair struct {left: Left, right: Right} fn take(p: Pair) -> Left {let Pair {left, right} = p; left}";
    for body in [
        "let p = Pair {left: Left {}, right: Right {}}; p.left = Left {}; 42",
        "let p = Pair {left: Left {}, right: Right {}}; p = Pair {left: take(p), right: Right {}}; 42",
    ] {
        cases.push(format!("{pair} fn main() -> usize {{{body}}}"));
    }
    cases.push("type Owner struct {tag: usize} where (tag == 7); impl Drop for Owner {fn drop(self){}} type Holder struct {reference: &usize, tag: usize} where (fact live = *reference == 7; live); impl Drop for Holder {fn drop(self){proof receiver_valid: self::live;}} fn main() -> usize {let owner = Owner {tag: 7}; let value = Holder {reference: &owner.tag, tag: 42}.tag; drop(owner); value}".into());
    for (index, source) in cases.iter().enumerate() {
        let program = verify(source).unwrap_or_else(|error| panic!("{error}: {source}"));
        let (value, events) = program.run_with_events().unwrap();
        let expected = match value {
            crate::interpreter::Value::Machine(_, n) => i32::from(n as u8),
            crate::interpreter::Value::Bool(b) => i32::from(b),
            crate::interpreter::Value::Unit => 0,
            other => panic!("unexpected native value: {other}"),
        };
        let mut modes = vec![(TraceMode::Value, expected)];
        if !program.drops.is_empty() {
            let ids = program
                .drops
                .iter()
                .enumerate()
                .map(|(i, name)| (format!("drop {name}"), i as u64 + 1))
                .collect::<BTreeMap<_, _>>();
            let order = events.iter().fold(0u64, |h, event| {
                h.wrapping_mul(167).wrapping_add(ids[event])
            });
            modes.push((TraceMode::Count, i32::from(events.len() as u8)));
            modes.push((TraceMode::Order, i32::from(order as u8)));
        }
        for (mode_index, (mode, expected)) in modes.into_iter().enumerate() {
            let binary =
                emit_mode(&program, mode).unwrap_or_else(|error| panic!("{error}: {source}"));
            assert_eq!(binary, emit_mode(&program, mode).unwrap());
            assert_eq!(&binary[..4], b"\x7fELF");
            let path = directory.join(format!("{index}-{mode_index}"));
            let status = execute_test_binary(&path, &binary, source);
            assert_eq!(
                status.code(),
                Some(expected),
                "native/interpreter disagreement: {source}"
            );
        }
    }
    // These exceed the interpreter's separate host-stack budget; execute
    // bounded native images directly and check the exact guard boundary.
    let recursive = "fn count(n: usize) -> usize ensures(result == n) decreases(n) {if n == 0 {0} else {count(n - 1) + 1}}";
    for (n, expected) in [(127, 127), (128, 125), (1000, 125)] {
        let source = format!("{recursive} fn main() -> usize {{count({n})}}");
        let program = verify(&source).unwrap();
        let binary = emit(&program).unwrap();
        let status = execute_test_binary(&directory.join(format!("limit-{n}")), &binary, &source);
        assert_eq!(status.code(), Some(expected));
    }
    let spin = "fn spin() -> usize ensures(false) {spin()} fn main() -> usize {spin()}";
    let binary = emit(&verify(spin).unwrap()).unwrap();
    assert_eq!(
        execute_test_binary(&directory.join("divergent"), &binary, spin).code(),
        Some(125)
    );
    // The library copy loop must not consume a native recursive activation for
    // each element. This length exceeds the recursion guard by a wide margin.
    let copied = "fn main() -> usize {let source: unique(usize, 4096) = alloc(4096, 42); let target: unique(usize, 4096) = alloc(4096, 0); vec::copy_prefix(&*source, &*target, 4096, 0); if (*target)[0] == 42 && (*target)[2048] == 42 && (*target)[4095] == 42 {42} else {1}}";
    let program = verify(copied).unwrap();
    assert!(program.trusted_assumptions().is_empty());
    let binary = emit(&program).unwrap();
    assert_eq!(
        execute_test_binary(&directory.join("large-buffer-copy"), &binary, copied).code(),
        Some(42)
    );
    let source = format!("{recursive} fn main() -> usize {{count(127) + count(127)}}");
    let binary = emit(&verify(&source).unwrap()).unwrap();
    assert_eq!(
        execute_test_binary(&directory.join("repeated-recursion"), &binary, &source).code(),
        Some(254)
    );
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_syscalls_write_exact_bytes_and_preserve_results() {
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("evergreen-io-{}-{stamp}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let hello = include_str!("../../../examples/hello.evg").to_owned();
    let packed = "extern syscall(1) fn write(fd: usize, bytes: &[u8; 3], count: usize) -> isize where(count <= 3); proof {trustme} fn main() -> usize {let bytes: [u8; 3] = [195, 169, 10]; if write(1, &bytes, 3) == 3 {0} else {1}}";
    let error = "extern syscall(1) fn write(fd: usize, byte: &u8, count: usize) -> isize where(count <= 1); proof {trustme} fn main() -> usize {let byte: u8 = 42; if write(usize::MAX, &byte, 1) == -9 {0} else {1}}";
    let eof = "extern syscall(0) fn read(fd: usize, byte: &u8, count: usize) -> isize where(count <= 1) modifies(byte) ensures(result == 0 => *byte == old(*byte)); proof {trustme} fn main() -> usize {let byte: u8 = 42; let received = read(0, &byte, 1); if received == 0 && byte == 42 {0} else {1}}";
    let pid = "extern syscall(39) fn getpid() -> isize; proof {trustme} fn main() -> usize {if getpid() > 0 {0} else {1}}";
    let large_bytes = std::iter::repeat_n("65", 257).collect::<Vec<_>>().join(",");
    let large = format!("{} fn main() -> usize {{let bytes: [u8; 257] = [{large_bytes}]; if linux_io::print_bytes(257, &bytes) == 257 {{0}} else {{1}}}}", concat!(include_str!("../../../stdlib/linux_io/linux_io.evg"), "\u{1e}"));
    let large_expected = vec![65; 257];
    let empty = format!("{} fn main() -> usize {{let bytes: [u8; 0] = []; if linux_io::print_bytes(0, &bytes) == 0 {{0}} else {{1}}}}", concat!(include_str!("../../../stdlib/linux_io/linux_io.evg"), "\u{1e}"));
    let prefix = format!("{} fn main() -> usize {{let bytes: [u8; 3] = [65, 66, 67]; if linux_io::write(1, &bytes, 2) == 2 {{0}} else {{1}}}}", concat!(include_str!("../../../stdlib/linux_io/linux_io.evg"), "\u{1e}"));
    for (source, expected) in [
        (hello.as_str(), b"Hello, Evergreen\n".as_slice()),
        (
            r#"fn main() -> usize {if linux_io::print_bytes(&"λ\0🦀\n") == 8 {0} else {1}}"#,
            "λ\0🦀\n".as_bytes(),
        ),
        (
            r#"fn main() -> usize {if linux_io::print_bytes(&"") == 0 {0} else {1}}"#,
            b"".as_slice(),
        ),
        (large.as_str(), large_expected.as_slice()),
        (prefix.as_str(), b"AB".as_slice()),
        (empty.as_str(), b"".as_slice()),
        (packed, "é\n".as_bytes()),
        (error, b"".as_slice()),
        (pid, b"".as_slice()),
        (eof, b"".as_slice()),
    ] {
        let program = verify(source).unwrap();
        let binary = emit(&program).unwrap();
        let output = directory.join("stdout");
        let stdout = fs::File::create(&output).unwrap();
        let status =
            execute_test_binary_to(&directory.join("program"), &binary, source, stdout.into());
        assert_eq!(status.code(), Some(0), "{source}");
        assert_eq!(fs::read(&output).unwrap(), expected, "{source}");
    }
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_heap_storage_is_independent_of_inline_and_interpreter_budgets() {
    let source =
        "fn main() -> u8 {let a: unique(u8, 17825792) = alloc(17825792, 42); (*a)[17825791]}";
    let program = verify(source).unwrap();
    assert!(program.run().unwrap_err().contains("before allocation"));
    let path = std::env::temp_dir().join(format!("evergreen-large-heap-{}", std::process::id()));
    let status = execute_test_binary(&path, &emit(&program).unwrap(), source);
    std::fs::remove_file(path).unwrap();
    assert_eq!(status.code(), Some(42));
}
