#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if ! command -v node >/dev/null 2>&1; then
  echo "STOPPED: node 20 or newer is missing. Ask your owner to install it, then run this again."
  exit 2
fi

major="$(node -p 'process.versions.node.split(".")[0]')"
if [ "$major" -lt 20 ]; then
  echo "STOPPED: node $major is too old, version 20 or newer is needed. Tell your owner."
  exit 2
fi

exec node "$here/mg.mjs" "$@"
