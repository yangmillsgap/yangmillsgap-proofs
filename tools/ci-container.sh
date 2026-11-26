#!/usr/bin/env bash
set -euo pipefail

phase="$1"
file="${2:-}"
proofs=/opt/proofs
base=/work/base
pr=/work/pr
out=/work/out

rm -rf "$proofs/MassGap" "$proofs/statements" "$proofs/tools"
cp -R "$base/MassGap" "$proofs/MassGap"
cp -R "$base/statements" "$proofs/statements"
cp -R "$base/tools" "$proofs/tools"
cp "$base/CheckLemma.lean" "$base/MassGap.lean" "$proofs/"

cd "$proofs"

if [ "$phase" = "build" ]; then
  exec node "$proofs/tools/check-step.mjs" --proofs "$proofs" --pr "$pr" --file "$file" \
    --in-place --phase build --out "$out" --json "$out/build.json" --time-limit 1200
fi

if [ "$phase" = "semantic" ]; then
  stem="$(basename "$file" .lean)"
  exec node "$proofs/tools/check-step.mjs" --proofs "$proofs" --pr "$pr" --file "$file" \
    --in-place --phase semantic --build-imports --olean "/work/olean/$stem.olean" \
    --json "$out/semantic.json" --time-limit 900
fi

if [ "$phase" = "controls" ]; then
  rm -rf "$proofs/controls"
  cp -R "$base/controls" "$proofs/controls"
  exec node "$proofs/tools/run-controls.mjs" --proofs "$proofs" --json "$out/controls.json"
fi

echo "FAULT: unknown phase $phase"
exit 2
