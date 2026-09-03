# Pancake rules and project conventions (read before writing any `.pnk`)

Empirically verified against the prebuilt `cake` (CakeML e8eca63, 2026-08-24).

## Language facts
* One translation unit: `guest/build.sh` runs `cpp -P -w -nostdinc -I guest/src -x c` over
  the source, so `#include "..."` and `#define` work. Avoid `'` in comments (cpp).
* Words are 64-bit. **No hex literals** (use decimal or `#define`). Negative literals
  like `-5` work (two's complement); `0 - 1` also fine.
* Operators: `+ - *`, `& | ^`, `<<`, `>>>` (LOGICAL right shift), `>>` (ARITHMETIC right
  shift - almost never what you want), `#>>` rotate right, `!` boolean not,
  `&& ||` logical. **No division or modulo** — use `udivmod/udiv/umod` in `lib/arith.pnk`.
  No 64x64->128 multiply: split into 32-bit halves.
* Comparisons: `< <= > >=` are SIGNED; `<+ <=+ >+ >=+` are UNSIGNED. `== !=`.
  They produce ordinary 0/1 expressions. Use unsigned for addresses/lengths. Bitwise
  ops bind tighter than comparisons.
* **Function calls are statements, never expressions.** Allowed forms only:
  `var 1 x = f(a);` (declaring call: shape annotation REQUIRED), `x = f(a);`,
  `f(a);`, `return f(a);`. Never `g(f(a))`, `f(a) + 1`, `if f(a) {`.
  In particular, `st ev + EV_OUTPUT, alloc(8)` is invalid; bind the result first:
  `var 1 empty = alloc(8);`.
  For expression-level helpers use cpp macros (see `ROTR32`, `LD_LE32` in `config.h`).
* Locals: `var x = e;` (shape 1 default), `var {1,1} p = <a, b>;` structs.
  Field access `p.0`. Struct-returning functions: `fun {1,1} f(...) { return <a,b>; }`.
  Struct literals can be passed directly as call arguments, and flat 8-field structs
  can be returned.
  Loading a struct from memory: `lds {1,1,1,1} addr`; storing: `st addr, structval`.
  Shape `4` == `{1,1,1,1}`.
* Memory: `ld8 e` (byte, zero-extended), `ld32 e`, `lds 1 e` (word, 8-aligned),
  `st8 a, v`, `st32 a, v`, `st a, v`. Load has LOWER precedence than arithmetic:
  `ld8 p + 1` == `ld8 (p + 1)`. ALWAYS parenthesize: `(ld8 (p + 1)) & 255`.
  Shared (MMIO) memory: `!ldw x, addr;` `!ld8 x, addr;` (statements) and
  `!stw addr, v;` `!st8 addr, v;`.
* Control: `if c { } else { }` (braces required), `while c { }`, `break;`,
  `continue;`, `skip;`. Every function must end with `return`.
* Globals: `var 1 g = 0;` at top level; assign from any function. A `catch` variable
  must be a LOCAL declared before the `try`.
* Exceptions: `exception Name : 1;` at top level; `throw Name expr;`;
  `try x = f(a) catch Name => localvar { ... }` (only a single call between try/catch).
  The result variable (including a struct-shaped one) must be declared before the `try`.
  Throwing from a `catch` handler is valid and translates the exception.
* `__add_with_carry__(a, b, cin)` treats `cin` as boolean: every nonzero value means
  one. Use it only as a declaration or assignment RHS.
* Reserved words include `in`, `st`, `tick`, `skip`, and `true`/`false`; using one as a
  variable gives a parse error at its first USE, not at the declaration.
* `@base` is heap start (0xa1000000). Do NOT use `@top` (broken in this build);
  the heap ends at `HEAP_END`. FFI: `@halt(@base,0,@base,0)`, `@trap(...)` (runtime/start.S).
* `inline fun` exists but a call is still a statement.
* Forward references and mutual recursion between top-level functions work.

## Project conventions
* Bytes = `<ptr, len>` pairs (shape `{1,1}`) pointing into the heap; input bytes live in
  the copied input blob (read-only by convention).
* Allocation: `alloc(n)` (8-byte aligned bump), `heap_mark()` / `heap_release(m)` for
  scratch. No free. A global scratch pointer allocated lazily inside a mark/release
  region dangles after release and may later be overwritten; allocate such state in an
  explicit `*_init()` called before the region.
* Slice arrays: element i is `<ptr,len>` at `arr + i*16` (`SLICE_PTR/SLICE_LEN` macros).
* U256 = shape `{1,1,1,1}` = 4 little-endian 64-bit limbs (`.0` least significant).
  In memory: 4 words, limb 0 at the lowest address (`lds {1,1,1,1} p` / `st p, v`).
  Big-endian 32-byte encodings are converted explicitly.
* Errors: one exception per domain (`SszErr`, `RlpErr`, ...), payload = small error code.
* Every module header names the SpecRef Lean file(s) it ports; keep function names
  aligned with the Lean/Python names.
* Word constants >= 2^63 must be written as negative decimals (signed 64-bit). Never
  hand-compute large constants: generate limb decimals with Python; this avoids wrong
  system addresses and similar transcription errors.

* Register pressure: ~30 live locals compile but spill; order statements for short live ranges
  in hot loops.

## Lessons from recent work

* Scratch buffers are allocated by explicit `*_init()` functions called from
  `main()`; never allocate them lazily inside a scratch mark/release region.
  Unit tests must call the same init functions as the main guest; see
  `guest/test/t_recover.pnk` for the pattern.
* `DBG(k)` expands to `skip` when `GUEST_DEBUG` is not defined. Debug markers
  therefore disappear from the default build; `DEBUG=1 guest/build.sh ...`
  enables the output stores.

## Tooling
* Unit tests: `guest/test/t_*.pnk` (a `main` that reads `input_blob()`, computes, and
  `output_write`s the result), checked with `tools/unit.py TEST INPUT 'python-expr'`.
  `tools/unit.py TEST INPUT @file.py` uses `expected(blob)` from the file as the oracle.
* `output_write(src, n)` writes from output offset 0: accumulate multi-record test output in a
  heap buffer and write once.
* `uv run --directory DIR ...` resolves relative paths against `DIR`, not the directory
  from which `uv` was invoked.
* `@trap` appears as `halted cleanly` in `spike_run`; the only output is marker byte `0xEE`
  at output offset 32.
* `objdump -d` shows cake's `.text` as `.word` data; to disassemble use
  `objcopy -O binary -j .text` then
  `objdump -D -b binary -m riscv:rv64 --adjust-vma=0x80000000`.
