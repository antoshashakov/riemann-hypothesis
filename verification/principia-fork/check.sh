#!/usr/bin/env bash
set -euo pipefail
ulimit -Sn 65536
export RUST_MIN_STACK=8388608
task=${1:?}
if [[ $task == storage ]]; then
  # The GitHub-hosted VM is ephemeral. Only its unused preinstalled SDKs are removed.
  test "$RUNNER_ENVIRONMENT" = github-hosted
  sudo rm -rf /usr/local/lib/android /usr/local/.ghcup /opt/ghc /usr/share/dotnet /usr/share/swift
  if ! command -v mkfs.btrfs >/dev/null; then
    sudo apt-get -qq update
    sudo apt-get -qq install btrfs-progs
  fi
  # zstd compresses the large serialized expressions while preserving mmap access.
  scratch=$(mktemp -d "$RUNNER_TEMP/proof-disk.XXXXXX")
  img=$(mktemp "$scratch/lean.XXXXXX")
  truncate -s 170G "$img"
  mkfs.btrfs -q "$img"
  mkdir "$scratch/mount"
  sudo mount -o loop,compress-force=zstd:5 "$img" "$scratch/mount"
  sudo chown "$(id -u):$(id -g)" "$scratch/mount"
  echo "RH_VOLUME=$scratch/mount" >> "$GITHUB_ENV"
  echo "ELAN_HOME=$scratch/mount/elan" >> "$GITHUB_ENV"
  echo "MATHLIB_CACHE_DIR=$scratch/mount/mathlib-cache" >> "$GITHUB_ENV"
  echo "$scratch/mount/elan/bin" >> "$GITHUB_PATH"
  df -h "$RUNNER_TEMP" "$scratch/mount"
  free -h
  exit 0
fi
project="$RH_VOLUME/proof"
if [[ $task == seed ]]; then
  mkdir "$project"
  git -C "$project" init -q
  git -C "$project" remote add origin https://github.com/antoshashakov/riemann-hypothesis.git
  git -C "$project" fetch -q --depth=2 origin "$CANDIDATE"
  test "$(git -C "$project" rev-parse "$CANDIDATE^")" = "$BASE"
  git -C "$project" -c advice.detachedHead=false checkout -q --detach "$BASE"
  cd "$project"
  curl --retry 3 -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$RUNNER_TEMP/elan-init.sh"
  sh "$RUNNER_TEMP/elan-init.sh" -y --default-toolchain none --no-modify-path
  lake --version
  # The official cache client is run at the base, before any proof source changes.
  for attempt in 1 2 3; do
    if lake exe mathlib/cache get; then break; fi
    if [[ $attempt == 3 ]]; then exit 1; fi
  done
  source scripts/cache-env.sh
  export LAKE_CACHE_DIR="$project/.lake/cache"
  mkdir "$RUNNER_TEMP/rh-curl"
  printf 'parallel-max = 160\n' > "$RUNNER_TEMP/rh-curl/.curlrc"
  CURL_HOME="$RUNNER_TEMP/rh-curl" python3 scripts/ci-cache-get.py --jobs 4
  test -s .lake/build/lib/lean/Main.olean
  git -c advice.detachedHead=false checkout -q --detach "$CANDIDATE"
  test "$(git rev-parse HEAD)" = "$CANDIDATE"
  # Remove the cached oleans of all modules deleted by this PR before either check.
  python3 - "$BASE" "$CANDIDATE" <<'PY'
import pathlib, subprocess, sys
files = subprocess.check_output(["git","diff","--name-only","--diff-filter=D",*sys.argv[1:],"--","src"], text=True).splitlines()
assert len(files) == 181
root = pathlib.Path(".lake/build/lib/lean")
for src in files:
    rel = pathlib.PurePosixPath(src).relative_to("src")
    assert rel.suffix == ".lean" and ".." not in rel.parts
    (root / rel.with_suffix(".olean")).unlink()
PY
  # Leave the working tree and public cache unchanged from here on.
  df -h "$RUNNER_TEMP" .
  # Page out inactive parts of the declaration graph on this disposable VM.
  # Cap the new swap file so the build keeps at least 10 GiB of physical disk.
  avail=$(df -BG --output=avail "$RUNNER_TEMP" | tail -1 | tr -d ' G')
  extra=$((avail - 10))
  if (( extra > 24 )); then extra=24; fi
  if (( extra >= 2 )); then
    sw=$(mktemp "$RUNNER_TEMP/rh-swap.XXXXXX")
    chmod 600 "$sw"
    fallocate -l "${extra}G" "$sw"
    sudo mkswap "$sw" >/dev/null
    sudo swapon "$sw"
  fi
  free -h
  exit 0
fi
cd "$project"
test "$(git rev-parse HEAD)" = "$CANDIDATE"
git diff --exit-code HEAD -- src lakefile.toml lake-manifest.json lean-toolchain
lib=.lake/build/lib/lean
overlay="$RH_VOLUME/link"
rel=Development/AbelianVarietyTheory/Proofs/DivisorProofs/AutomorphicFormsFiniteGL
if [[ $task == link ]]; then
  mkdir -p "$overlay/$(dirname "$rel")"
  export LEAN_PATH="$overlay:$(lake env printenv LEAN_PATH)"
  opts=(-j1 -t0 --tstack=400000 -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxHeartbeats=4000000 -DwarningAsError=true --root=src)
  /usr/bin/time -v lean "${opts[@]}" -o "$overlay/$rel.olean" "src/$rel.lean"
  /usr/bin/time -v lean "${opts[@]}" -o "$overlay/Main.olean" src/Main.lean
elif [[ $task == build ]]; then
  # Standard dependency traces cause stock Lake to re-elaborate the entire affected cone.
  export LAKE_ARTIFACT_CACHE=false
  /usr/bin/time -v lake --rehash build Main
  test -s "$lib/Main.olean"
  exit 0
elif [[ $task != audit ]]; then
  exit 2
fi
cat > "$RUNNER_TEMP/Axioms.lean" <<'LEAN'
import Main
set_option pp.width 200
#print axioms riemannHypothesis
#print axioms riemannZeta_eq_zero_re
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
#print axioms LFunction_eq_zero_re_of_isPrimitive
LEAN
if [[ $task == audit ]]; then export LEAN_PATH="$(lake env printenv LEAN_PATH)"; fi
/usr/bin/time -v lean -j1 -t0 --tstack=400000 "$RUNNER_TEMP/Axioms.lean" | tee "$RUNNER_TEMP/axioms-$task.log"
test "$(grep -Fc 'depends on axioms: [propext, Classical.choice, Quot.sound]' "$RUNNER_TEMP/axioms-$task.log")" = 5
