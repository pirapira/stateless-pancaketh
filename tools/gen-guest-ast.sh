#!/usr/bin/env bash
# gen-guest-ast.sh -- regenerate the Lean view of the guest, for both builds:
#   Guest/guest.pp.pnk           the cpp-expanded ZISK_ACCEL guest (the deployed
#                                build: crypto via accelerator @ffi calls)
#   Guest/Ast.lean               its parse by flapjack's parser (Guest.guestAst)
#   Guest/guest-software.pp.pnk  the default build (all crypto in Pancake)
#   Guest/SoftwareAst.lean       its parse (Guest.Software.guestAst)
# Both mirror the preprocessing step of guest/build.sh (no GUEST_DEBUG).
# Re-run after editing guest/src and commit the four files; Lake does not
# track guest/src itself. `lake build` then re-checks (Guest/AstParse.lean)
# that each committed AST is what the parser produces from its source.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
CPP="${CPP:-cpp}"
cd "$HERE"
lake build gen-guest-ast >/dev/null

gen() { # gen <cpp flags> <pp output> <lean output> <namespace>
  local flags=$1 pp=$2 lean=$3 ns=$4
  # shellcheck disable=SC2086
  "$CPP" $flags -P -w -nostdinc -I guest/src -x c guest/src/main.pnk \
    | grep -v '^#' > "$pp"
  echo "wrote $pp ($(wc -l < "$pp") lines)"
  lake exe gen-guest-ast "$pp" "$ns" > "$lean"
  echo "wrote $lean ($(wc -l < "$lean") lines)"
}

gen "-DZISK_ACCEL" Guest/guest.pp.pnk Guest/Ast.lean Guest
gen "" Guest/guest-software.pp.pnk Guest/SoftwareAst.lean Guest.Software

# Stamp the source hashes into Guest/Source.lean so Lake rebuilds the
# include_str% embeddings (it tracks only the .lean file's own content).
for f in guest.pp.pnk guest-software.pp.pnk; do
  h=$(sha256sum "Guest/$f" | cut -d' ' -f1)
  sed -i "s|^-- $f sha256: .*|-- $f sha256: $h|" Guest/Source.lean
done
echo "stamped source hashes into Guest/Source.lean"
