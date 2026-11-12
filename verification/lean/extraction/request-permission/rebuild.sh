#!/bin/sh
set -eu
capture=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
isolated=$1
aeneas=$2
opam_root=$3
if [ -e "$isolated/src" ]; then
  printf '%s\n' "Use a fresh isolated replay tree" >&2
  exit 2
fi
mkdir -p "$isolated"
git -C "$aeneas" archive ab34bd28458a08c150b7cbf1873e59af74588138 src |
  tar -xf - -C "$isolated"
ln -s "$aeneas/charon" "$isolated/charon"
patch --silent -d "$isolated" -p1 < "$capture/checked-selective-lift.patch"
opam exec --root="$opam_root" --switch=aeneas-5.3.0 -- dune build --root "$isolated/src" -j 2
"$isolated/src/_build/default/main.exe" -backend lean -checks -sequential \
  -no-progress-bar -print-error-emitters -split-files \
  -dest "$isolated/replayed" "$capture/arithmetic.llbc"
diff -qr "$isolated/replayed" "$capture/Arithmetic"
