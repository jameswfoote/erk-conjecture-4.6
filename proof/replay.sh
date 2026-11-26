#!/bin/sh
set -eu
while read -r package pinned; do
    actual=$(git -C ".lake/packages/$package" rev-parse HEAD)
    if [ "$actual" != "$pinned" ]; then
        echo "Revision mismatch for $package: $actual" >&2
        exit 1
    fi
    if [ "$package" = mathlib ]; then printf 'mathlib %s\n' "$actual"; fi
done <<'END_REVS'
mathlib c98ae54af00eaefe79c51b2b278361ca94e59bfb
plausible 0203092c2e5e26edf967000f0e177cf31c72e17a
LeanSearchClient 2ed4ba69b6127de8f5c2af83cccacd3c988b06bf
importGraph 3611075024b3529e5798e53c733671039f06f0bd
proofwidgets 45777338ffb69576c945dfe9466665b8023a8b8c
aesop a2e4d9e9aebdbdce1ce6b6f0a19dd49e0120c990
Qq 9bff22d64abde45944c7b1f55bce6c89dd8307e6
batteries ffad3f5b7ebe1ac3e09779ec8a863a5138c1246c
Cli cd188c6ecfbf6c00cf639e4d4fb18bf773ce8c2c
END_REVS
version=$(lean --version)
printf '%s\n' "$version"
case "$version" in
    *"version 4.25.2,"*"commit b86e2e5824bcdbfa0e8d02dd97b4c48792a385d1,"*) ;;
    *) echo "Unexpected Lean toolchain" >&2; exit 1 ;;
esac
build=$(mktemp -d)
trap 'rm -rf "$build"' 0
export LEAN_PATH="$build:${LEAN_PATH:-}"
for name in Continuation FastSpectrum Model Scalar Singular Lift Source Transport EnzymeBlock FirstLift Target EnzymeGraph PhysicalPositive SecondLift Common Bistability Audit; do
    printf 'Checking %s.lean\n' "$name"
    if output=$(lean -j1 --root=. -o "$build/$name.olean" "$name.lean"); then
        printf '%s\n' "$output"
    else
        printf '%s\n' "$output" >&2
        exit 1
    fi
done
cat > "$build/Seal.lean" <<'END_LEAN'
import Bistability
example : ERK.Target.Conjecture46 := ERK.conjecture_4_6
#print axioms ERK.conjecture_4_6
END_LEAN
output=$(lean -j1 --root="$build" "$build/Seal.lean")
printf '%s\n' "$output"
test "$output" = "'ERK.conjecture_4_6' depends on axioms: [propext, Classical.choice, Quot.sound]"
printf 'Checked all 17 project modules.\n'
