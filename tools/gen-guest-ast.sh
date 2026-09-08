#!/usr/bin/env bash
# gen-guest-ast.sh -- regenerate the Lean view of the guest:
#   Guest/guest.pp.pnk  the cpp-expanded guest source (as guest/build.sh
#                       preprocesses it for the default build: no GUEST_DEBUG,
#                       no ZISK_ACCEL)
#   Guest/Ast.lean      its parse by flapjack's Pancake parser, as Lean terms
# Re-run after editing guest/src and commit both files; Lake does not track
# guest/src itself. `lake build` then re-checks (Guest/AstParse.lean) that the
# committed AST is what the parser produces from the committed source.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
CPP="${CPP:-cpp}"
"$CPP" -P -w -nostdinc -I "$HERE/guest/src" -x c "$HERE/guest/src/main.pnk" \
  | grep -v '^#' > "$HERE/Guest/guest.pp.pnk"
echo "wrote Guest/guest.pp.pnk ($(wc -l < "$HERE/Guest/guest.pp.pnk") lines)"
(cd "$HERE" && lake build gen-guest-ast >/dev/null && \
  lake exe gen-guest-ast Guest/guest.pp.pnk > Guest/Ast.lean)
echo "wrote Guest/Ast.lean ($(wc -l < "$HERE/Guest/Ast.lean") lines)"
