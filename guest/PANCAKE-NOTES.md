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
  Use unsigned for addresses/lengths. Bitwise ops bind tighter than comparisons.
* **Function calls are statements, never expressions.** Allowed forms only:
  `var 1 x = f(a);` (declaring call: shape annotation REQUIRED), `x = f(a);`,
  `f(a);`, `return f(a);`. Never `g(f(a))`, `f(a) + 1`, `if f(a) {`.
  For expression-level helpers use cpp macros (see `ROTR32`, `LD_LE32` in `config.h`).
* Locals: `var x = e;` (shape 1 default), `var {1,1} p = <a, b>;` structs.
  Field access `p.0`. Struct-returning functions: `fun {1,1} f(...) { return <a,b>; }`.
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
* Reserved words include `in`, `st`, `tick`, `skip`, `true`, `false`.
* `@base` is heap start (0xa0100000). Do NOT use `@top` (broken in this build);
  the heap ends at `HEAP_END`. FFI: `@halt(@base,0,@base,0)`, `@trap(...)` (runtime/start.S).
* `inline fun` exists but a call is still a statement.

## Project conventions
* Bytes = `<ptr, len>` pairs (shape `{1,1}`) pointing into the heap; input bytes live in
  the copied input blob (read-only by convention).
* Allocation: `alloc(n)` (8-byte aligned bump), `heap_mark()` / `heap_release(m)` for
  scratch. No free.
* Slice arrays: element i is `<ptr,len>` at `arr + i*16` (`SLICE_PTR/SLICE_LEN` macros).
* U256 = shape `{1,1,1,1}` = 4 little-endian 64-bit limbs (`.0` least significant).
  In memory: 4 words, limb 0 at the lowest address (`lds {1,1,1,1} p` / `st p, v`).
  Big-endian 32-byte encodings are converted explicitly.
* Errors: one exception per domain (`SszErr`, `RlpErr`, ...), payload = small error code.
* Every module header names the SpecRef Lean file(s) it ports; keep function names
  aligned with the Lean/Python names.
* Unit tests: `guest/test/t_*.pnk` (a `main` that reads `input_blob()`, computes, and
  `output_write`s the result), checked with `tools/unit.py TEST INPUT 'python-expr'`.
