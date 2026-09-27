#!/usr/bin/env bash
# usage:
#   bash sh/setup.sh [--clean|-clean] [vX.Y.Z]
# default version: v4.33.1
#
# Full port of ps1/setup.ps1 for Linux/WSL: Lean toolchain (manual tarball),
# lean-toolchain, mathlib tag, lake-manifest sync, packages, clean, cache, build.
# Note: ps1/setup.ps1 calls .\ps1\run.ps1 at the end; this script intentionally
# does NOT call sh/run.sh (setup sets up/builds; leave run to the user).

set -euo pipefail

CLEAN=false
VERSION="v4.33.1"
for arg in "$@"; do
  case "$arg" in
    --clean|-clean) CLEAN=true ;;
    v[0-9]*) VERSION="$arg" ;;
    *)
      echo "usage: bash sh/setup.sh [--clean|-clean] [vX.Y.Z]" >&2
      exit 1
      ;;
  esac
done

VERSION_NUMBER="${VERSION#v}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

if [[ -f "$HOME/.elan/env" ]]; then
  # shellcheck source=/dev/null
  source "$HOME/.elan/env"
fi

if ! command -v elan >/dev/null 2>&1; then
  echo "error: elan not found on PATH. Install elan first (https://github.com/leanprover/elan), then re-run." >&2
  exit 1
fi

# Manual Lean install (mirror ps1/setup.ps1). Do NOT use `elan toolchain install`
# — it downloads via elan and fails on this network; we fetch the Linux tarball ourselves.
TOOLCHAIN_ROOT="$HOME/.elan/toolchains"
TARGET_NAME="leanprover--lean4---${VERSION}"
TARGET_DIR="${TOOLCHAIN_ROOT}/${TARGET_NAME}"
LEAN_BIN="${TARGET_DIR}/bin/lean"

if [[ -x "$LEAN_BIN" ]]; then
  echo "Lean ${VERSION} is already installed, skipping installing."
else
  mkdir -p "$TOOLCHAIN_ROOT"
  TAR_FILE="lean-${VERSION_NUMBER}-linux.tar.zst"
  TAR_PATH="${TOOLCHAIN_ROOT}/${TAR_FILE}"
  if [[ ! -f "$TAR_PATH" ]]; then
    URL="https://releases.lean-lang.org/lean4/${VERSION}/${TAR_FILE}"
    echo "Downloading Lean ${VERSION} from ${URL}..."
    if ! curl -fL --retry 3 -o "$TAR_PATH" "$URL"; then
      rm -f "$TAR_PATH"
      echo "error: failed to download Lean ${VERSION} from ${URL}" >&2
      exit 1
    fi
  fi
  mkdir -p "$TARGET_DIR"
  if tar --zstd --strip-components=1 -xf "$TAR_PATH" -C "$TARGET_DIR" 2>/dev/null; then
    :
  elif command -v unzstd >/dev/null 2>&1; then
    tar --use-compress-program=unzstd --strip-components=1 -xf "$TAR_PATH" -C "$TARGET_DIR"
  else
    echo "error: need tar with zstd support (or unzstd) to extract ${TAR_FILE}" >&2
    exit 1
  fi
  rm -f "$TAR_PATH"
  if [[ ! -x "$LEAN_BIN" ]]; then
    echo "error: extract finished but ${LEAN_BIN} is missing" >&2
    exit 1
  fi
  echo "✅ Lean ${VERSION} installed successfully."
fi

TOOLCHAIN="leanprover/lean4:${VERSION}"
elan default "$TOOLCHAIN"
elan override set "$TOOLCHAIN"
elan override unset --nonexistent 2>/dev/null || true
echo "✅ elan default and directory override set to ${TOOLCHAIN}"

needs_clean=false
if [[ ! -f lean-toolchain ]]; then
  echo "error: lean-toolchain not found in $(pwd)" >&2
  exit 1
fi
current_tc="$(tr -d '\r\n' < lean-toolchain)"
if [[ "$current_tc" == "$TOOLCHAIN" ]]; then
  echo "leanprover/lean4:${VERSION} is already set in lean-toolchain, skipping"
else
  needs_clean=true
  printf '%s\n' "$TOOLCHAIN" > lean-toolchain
  echo "✅ lean-toolchain updated to ${TOOLCHAIN}"
fi

name="mathlib"
packagePath=".lake/packages/${name}"

bootstrap_mathlib() {
  if ! command -v jq >/dev/null 2>&1; then
    echo "error: jq is required (e.g. apt install jq / conda install -c conda-forge jq)" >&2
    exit 1
  fi
  local url rev
  url="$(jq -r '.packages[] | select(.name=="mathlib") | .url' lake-manifest.json)"
  rev="$(jq -r '.packages[] | select(.name=="mathlib") | .rev' lake-manifest.json)"
  if [[ -z "$url" || "$url" == "null" || -z "$rev" || "$rev" == "null" ]]; then
    echo "error: mathlib url/rev not found in lake-manifest.json; cannot bootstrap" >&2
    exit 1
  fi
  echo "fetch mathlib at ${rev} from ${url} by shallow cloning (bootstrap)"
  mkdir -p "$packagePath"
  git -C "$packagePath" init
  git -C "$packagePath" remote add origin "$url"
  git -C "$packagePath" fetch --depth 1 origin "$rev"
  git -C "$packagePath" checkout --force "$rev"
}

if [[ ! -f "${packagePath}/lean-toolchain" ]]; then
  bootstrap_mathlib
fi

versionRegex='leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?)'
mathlib_tc="$(tr -d '\r\n' < "${packagePath}/lean-toolchain")"
if [[ "$mathlib_tc" =~ $versionRegex ]]; then
  mathlibVersion="${BASH_REMATCH[1]}"
else
  echo "error: Could not extract Lean version from mathlib lean-toolchain" >&2
  exit 1
fi

if [[ "$mathlibVersion" == "$VERSION" ]]; then
  echo "✅ mathlib already matches Lean version ${VERSION}. Skipping."
else
  echo "⏳ Checking out mathlib tag ${VERSION} (current: ${mathlibVersion})..."
  git -C "$packagePath" fetch --depth 1 origin tag "$VERSION"
  git -C "$packagePath" checkout --force "$VERSION"
fi

if ! command -v jq >/dev/null 2>&1; then
  echo "error: jq is required (e.g. apt install jq / conda install -c conda-forge jq)" >&2
  exit 1
fi

manifestFile="${packagePath}/lake-manifest.json"
if [[ ! -f "$manifestFile" ]]; then
  echo "error: lake-manifest.json not found in ${packagePath}" >&2
  exit 1
fi

mathlib_rev="$(git -C "$packagePath" rev-parse HEAD)"

# Sync ./lake-manifest.json from mathlib's: mathlib packages + mathlib itself
# (name mathlib, inputRev master, rev=HEAD). Update or add inputRev/rev only.
# This keeps proofwidgets (and other deps) on revs whose lean-toolchain matches
# the project toolchain — avoiding e.g. PW on v4.33.0 while the project is on v4.33.1.
new_manifest="$(jq -n \
  --slurpfile proj lake-manifest.json \
  --slurpfile ml "$manifestFile" \
  --arg mrev "$mathlib_rev" '
  ($ml[0].packages + [{name: "mathlib", inputRev: "master", rev: $mrev}]) as $sources
  | $proj[0] as $base
  | reduce $sources[] as $s ($base;
      ($s.name) as $n
      | if any(.packages[]; .name == $n) then
          .packages |= map(
            if .name == $n then
              .inputRev = $s.inputRev | .rev = $s.rev
            else . end
          )
        else
          .packages += [$s]
        end
    )
  ')"

_new_mani="$(mktemp)"
_old_mani="$(mktemp)"
printf '%s\n' "$new_manifest" | jq -c '.' > "$_new_mani"
jq -c '.' lake-manifest.json > "$_old_mani"
if ! cmp -s "$_old_mani" "$_new_mani"; then
  jq '.' "$_new_mani" > lake-manifest.json
  echo "🌟 lake-manifest.json updated successfully."
else
  echo "lake-manifest.json already in sync with mathlib."
fi
rm -f "$_new_mani" "$_old_mani"

# Shallow fetch/checkout each package from (updated) project lake-manifest.json
while IFS=$'\t' read -r url name rev; do
  [[ -n "$name" ]] || continue
  pkg=".lake/packages/${name}"
  if [[ -d "$pkg" ]]; then
    current_rev="$(git -C "$pkg" rev-parse HEAD 2>/dev/null || true)"
    if [[ "$current_rev" == "$rev" ]]; then
      echo "Package ${name} is already at revision ${rev}. Skipping fetch."
      continue
    fi
  else
    echo "fetch ${name} at ${rev} from ${url} by shallow cloning"
    mkdir -p "$pkg"
    git -C "$pkg" init
    git -C "$pkg" remote add origin "$url"
  fi
  git -C "$pkg" fetch --depth 1 origin "$rev"
  git -C "$pkg" checkout --force "$rev"
done < <(jq -r '.packages[] | [.url, .name, .rev] | @tsv' lake-manifest.json)

# ---------------------------------------------------------------------------
# ProofWidgets / Lake trap (read before changing this section)
# ---------------------------------------------------------------------------
# Dirty trees under .lake/packages (especially proofwidgets) break Lake's
# reuse of pre-built artifacts ("failed to reuse pre-built JS"). So every
# package is hard-reset to a clean tree at its manifest revision below.
# Local edits under .lake/packages WILL BE WIPED by this setup — intentional.
#
# Version alignment: mathlib was checked out to tag $VERSION and the project
# lake-manifest.json was synced from mathlib's, so proofwidgets (and friends)
# land on revs whose lean-toolchain matches the project when possible.
#
# Build strategy:
#   * `lake exe cache get` supplies Mathlib oleans (keep it).
#   * ProofWidgets widget JS is built DIRECTLY with Node via `lake build`
#     inside .lake/packages/proofwidgets, because Mathlib's errorOnBuild
#     blocks building it as a dependency, and reusing cached widget JS has
#     proven unreliable. Hence Node v22.20.0 is always ensured below.
# ---------------------------------------------------------------------------

# Hard-reset ALL packages to clean manifest revs. Even when HEAD already
# matches rev, dirty files / leftover outputs still break artifact reuse.
while IFS=$'\t' read -r url name rev; do
  [[ -n "$name" ]] || continue
  pkg=".lake/packages/${name}"
  if [[ ! -d "$pkg" ]]; then
    echo "warning: package ${name} missing at ${pkg}; skip clean reset" >&2
    continue
  fi
  echo "🧹 reset package ${name} to clean manifest rev ${rev}"
  if ! git -C "$pkg" cat-file -e "${rev}^{commit}" 2>/dev/null; then
    git -C "$pkg" fetch --depth 1 origin "$rev"
  fi
  git -C "$pkg" checkout --force "$rev"
  git -C "$pkg" reset --hard HEAD
  git -C "$pkg" clean -fd
done < <(jq -r '.packages[] | [.url, .name, .rev] | @tsv' lake-manifest.json)

start_ts="$(date +%s)"
if [[ "$needs_clean" == true || "$CLEAN" == true ]]; then
  echo "Lean toolchain changed recently — running lake clean"
  lake clean
fi

# Mathlib oleans come from the cache.
echo "⏳ lake exe cache get..."
lake exe cache get

# Ensure Node v22.20.0 (needed to build ProofWidgets widget JS).
NODE_VERSION="v22.20.0"
NODE_DIST="node-${NODE_VERSION}-linux-x64"
NODE_HOME="$HOME/.local/${NODE_DIST}"
NODE_TARBALL="${NODE_DIST}.tar.xz"
if [[ -x "${NODE_HOME}/bin/node" ]]; then
  echo "✅ Node ${NODE_VERSION} already present at ${NODE_HOME}"
else
  mkdir -p "$HOME/.local"
  local_tar=""
  for cand in "$HOME/.local/${NODE_TARBALL}" "$HOME/Downloads/${NODE_TARBALL}" "$HOME/${NODE_TARBALL}" "./${NODE_TARBALL}"; do
    if [[ -f "$cand" ]]; then local_tar="$cand"; break; fi
  done
  if [[ -n "$local_tar" ]]; then
    echo "Using local Node tarball ${local_tar}"
  else
    local_tar="$HOME/.local/${NODE_TARBALL}"
    NODE_URL="https://nodejs.org/dist/${NODE_VERSION}/${NODE_TARBALL}"
    echo "Downloading Node ${NODE_VERSION} from ${NODE_URL}..."
    if ! curl -fL --retry 3 -o "$local_tar" "$NODE_URL"; then
      rm -f "$local_tar"
      echo "error: failed to download Node ${NODE_VERSION} from ${NODE_URL}" >&2
      exit 1
    fi
  fi
  if ! tar -xJf "$local_tar" -C "$HOME/.local"; then
    echo "error: failed to extract ${local_tar}" >&2
    exit 1
  fi
  if [[ ! -x "${NODE_HOME}/bin/node" ]]; then
    echo "error: extract finished but ${NODE_HOME}/bin/node is missing" >&2
    exit 1
  fi
  echo "✅ Node ${NODE_VERSION} installed to ${NODE_HOME}"
fi
export PATH="${NODE_HOME}/bin:$PATH"
echo "node $(node -v), npm $(npm -v)"
if ! grep -qs "${NODE_DIST}/bin" "$HOME/.bashrc"; then
  echo "hint: add to ~/.bashrc:  export PATH=\"\$HOME/.local/${NODE_DIST}/bin:\$PATH\""
fi

# Build ProofWidgets (incl. widget JS) directly inside the package.
pw_path=".lake/packages/proofwidgets"
if [[ ! -d "$pw_path" ]]; then
  echo "error: ${pw_path} not found" >&2
  exit 1
fi
echo "⏳ build package proofwidgets (Node)..."
pushd "$pw_path" >/dev/null
if ! lake build; then
  popd >/dev/null
  echo "error: lake build in ${pw_path} failed" >&2
  exit 1
fi
popd >/dev/null

echo "⏳ building the entire project..."
lake build
lake build sympy.printing.echo
end_ts="$(date +%s)"
echo "🏁 Build completed in $((end_ts - start_ts)) seconds."
