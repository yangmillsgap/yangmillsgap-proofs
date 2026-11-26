#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

toolchain="$(cut -d: -f2 lean-toolchain | tr -d '[:space:]')"
tag="prebuilt-${toolchain}"
asset="massgap-lake-build-${toolchain}.tar.gz"
repo="$(node --input-type=module -e 'import("./tools/lib/config.mjs").then((m) => console.log(m.upstreamRepo()))')"
outdir="$root/dist"

lake build YMPublic MassGap.Defs MassGap.Statement

if find .lake/build -type l | grep -q .; then
  echo "STOPPED: .lake/build holds symbolic links, so the archive would not unpack safely"
  exit 2
fi

mkdir -p "$outdir"
rm -f "$outdir/$asset"
stage="$(mktemp -d)"
trap 'rm -rf "$stage"' EXIT

mkdir -p "$stage/.lake"
cp -R .lake/build "$stage/.lake/build"
rm -rf "$stage/.lake/build/lib/lean/MassGap/Outside" "$stage/.lake/build/ir/MassGap/Outside"
find "$stage/.lake/build" -name '*.setup.json' -delete
find "$stage/.lake/build" -name '*.trace' -exec env MG_ROOT="$root/" MG_HOME="$HOME" node -e '
const fs = require("node:fs");
for (let n = 1; n < process.argv.length; n++) {
  const theFile = process.argv[n];
  const theTrace = JSON.parse(fs.readFileSync(theFile, "utf8"));
  theTrace.log = [];
  const theText = JSON.stringify(theTrace);
  const theRelative = theText.split(process.env.MG_ROOT).join("");
  const theNeutral = theRelative.split(process.env.MG_HOME).join("~");
  fs.writeFileSync(theFile, theNeutral);
}
' {} +

if grep -rqF "$root" "$stage/.lake/build" || grep -rqF "$HOME" "$stage/.lake/build"; then
  echo "STOPPED: the archive would carry a local path of this machine"
  exit 2
fi

(cd "$stage" && COPYFILE_DISABLE=1 tar --no-xattrs --uid 0 --gid 0 --uname root --gname root -czf "$outdir/$asset" .lake/build)

sum="$(shasum -a 256 "$outdir/$asset" | cut -d' ' -f1)"
bytes="$(wc -c < "$outdir/$asset" | tr -d '[:space:]')"
url="https://github.com/${repo}/releases/download/${tag}/${asset}"
echo "we wrote dist/$asset ($bytes bytes)"
echo "sha256 $sum"
echo "upload it with: gh release create $tag dist/$asset --repo $repo"
echo "then set tag $tag, asset $asset, url $url, sha256 $sum and bytes $bytes in tools/prebuilt.json"
echo "to try it before uploading: MG_PREBUILT_FILE=$outdir/$asset tools/mg.sh setup"
