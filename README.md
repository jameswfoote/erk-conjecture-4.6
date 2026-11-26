# ERK Conjecture 4.6

**A proof of bistability at all processivity levels in a model of ERK regulation**

James Foote · University of British Columbia · [ORCID 0009-0004-3841-8020](https://orcid.org/0009-0004-3841-8020)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24556874.svg)](https://doi.org/10.5281/zenodo.24556874)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey.svg)](LICENSE)

This repository mirrors version 1.0.0 of the Zenodo record
[10.5281/zenodo.24556874](https://doi.org/10.5281/zenodo.24556874), published 26 November 2026.
The Zenodo record is the authoritative version. The manuscript, the Lean proof, the SageMath
certificate, and the verification files here are byte-for-byte copies of the published files.

## Result

The manuscript proves that for each prescribed pair of kinase and phosphatase processivities in
the open unit square, a single choice of thirteen positive rates and three positive totals supports
two distinct positive equilibria. Both are exponentially stable on the same nine-dimensional
stoichiometric class.

The statement is formalized in Lean 4 with mathlib as `ERK.conjecture_4_6` in
[`proof/Bistability.lean`](proof/Bistability.lean). The archived build prints it as:

```lean
ERK.conjecture_4_6 (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1) :
  ∃ k T,
    (∀ (i : Fin 13), 0 < k i) ∧
      (∀ (i : Fin 3), 0 < T i) ∧
        ERK.Model.kinaseProcessivity k = p ∧
          ERK.Model.phosphataseProcessivity k = q ∧
            ∃ x y, x ≠ y ∧ ERK.Target.PositiveClassSink k T x ∧ ERK.Target.PositiveClassSink k T y
'ERK.conjecture_4_6' depends on axioms: [propext, Classical.choice, Quot.sound]
```

It uses only Lean's three standard axioms. The comparison with the published model equations is in
[`proof/Source.lean`](proof/Source.lean).

## Contents

| Path | Contents |
| --- | --- |
| [`paper/ERK-Conjecture-4.6.pdf`](paper/ERK-Conjecture-4.6.pdf) | The five-page manuscript. |
| [`proof/`](proof/) | The 17 Lean modules, the toolchain pin (`lean-toolchain`), the Lake configuration (`lakefile.toml`), the pinned dependency manifest (`lake-manifest.json`), the mathlib import list, the replay script (`replay.sh`), and the original transcript (`replay.txt`). Extracted from `zenodo/lean-proof.zip`. |
| [`sage-certificate/prescribed-cubic-finite.py`](sage-certificate/prescribed-cubic-finite.py) | The exact SageMath certificate for the unequal-processivity example in Table 1. Extracted from `zenodo/sage-certificate.zip`. |
| [`verification/independent_erk_verification.py`](verification/independent_erk_verification.py) | An additional exact checker for the low- and high-saturation controls at a different prescribed pair. |
| [`verification/independent_erk_verification_results.txt`](verification/independent_erk_verification_results.txt) | Output of that checker under SageMath 10.10. |
| [`verification/verification-transcript.txt`](verification/verification-transcript.txt) | The Lean build output, theorem statements, and axiom inspection. Identical to `proof/replay.txt`. |
| [`zenodo/`](zenodo/) | The two published archives and the published Zenodo README, unchanged. |
| [`SHA256SUMS`](SHA256SUMS) | The SHA-256 digests published in the Zenodo README, listed against their paths in this repository. |
| [`CITATION.cff`](CITATION.cff) | Citation metadata. |
| [`LICENSE`](LICENSE) | Creative Commons Attribution 4.0 International. |

## Verify file integrity

From the repository root:

```sh
shasum -a 256 -c SHA256SUMS
```

To confirm that the browsable directories match the published archives:

```sh
tmp=$(mktemp -d)
unzip -q zenodo/lean-proof.zip -d "$tmp"
unzip -q zenodo/sage-certificate.zip -d "$tmp"
diff -r "$tmp/proof" proof && cmp "$tmp/prescribed-cubic-finite.py" sage-certificate/prescribed-cubic-finite.py && echo "Extracted files match the archives."
rm -rf "$tmp"
```

## Reproduce the Lean proof

You need a POSIX shell, Git, and the Lean toolchain manager [elan](https://github.com/leanprover/elan).
elan selects the pinned toolchain from `proof/lean-toolchain`. The first cache retrieval needs network
access on a fresh installation.

```sh
cd proof
xargs lake exe cache get < mathlib-imports.txt
lake env sh replay.sh > ../local-lean-transcript.txt
cd ..
tail -n 2 local-lean-transcript.txt
```

The replay script first checks that every dependency is at its pinned revision and that Lean is the
pinned version. It then compiles each project module in a fresh temporary directory, checks the
top-level proof against `ERK.Target.Conjecture46`, and prints its axioms. The expected last two lines
are:

```text
'ERK.conjecture_4_6' depends on axioms: [propext, Classical.choice, Quot.sound]
Checked all 17 project modules.
```

To compare the full output with the archived transcript:

```sh
diff verification/verification-transcript.txt local-lean-transcript.txt
```

The pinned toolchain is Lean 4.25.2 (commit `b86e2e5824bcdbfa0e8d02dd97b4c48792a385d1`), and mathlib is
pinned to `c98ae54af00eaefe79c51b2b278361ca94e59bfb`. The archived transcript was recorded on Apple
Silicon. Another host may print a different platform string on the Lean version line, which is the
only difference you should expect.

## Reproduce Table 1

With SageMath 10.10 installed, run this from the repository root. Python assertions must be enabled,
which is the Sage default.

```sh
sage -python sage-certificate/prescribed-cubic-finite.py
```

The certificate uses the exact rational inputs `p = 1/2`, `q = 2/3`, `K = 1024`, and
`delta = eta = 1/1000000`. It checks the equilibrium equations, the totals, and stability in physical
time. In order of increasing free S01 concentration, it reports **0, 0, 1** eigenvalues in the open
right half-plane. The printed concentrations are approximations of exact real algebraic values.

## Reproduce the additional checks

```sh
sage -python verification/independent_erk_verification.py > local-additional-results.txt
diff -u verification/independent_erk_verification_results.txt local-additional-results.txt
```

These checks use `p = 999/1000`, `q = 9999/10000`, and `delta = eta = 10^-12`. At `K = 1` there is one
positive equilibrium with no unstable directions. At `K = 1048576` the three positive equilibria have
**0, 1, 0** unstable directions in order of increasing free S11. These two controls and Table 1 are
finite examples. The Lean theorem establishes the statement for all pairs.

## Citation

Please cite the Zenodo record. GitHub's "Cite this repository" button reads [`CITATION.cff`](CITATION.cff).

```bibtex
@misc{foote2026erk,
  author    = {Foote, James},
  title     = {A proof of bistability at all processivity levels in a model of {ERK} regulation},
  year      = {2026},
  month     = nov,
  publisher = {Zenodo},
  version   = {1.0.0},
  doi       = {10.5281/zenodo.24556874},
  url       = {https://doi.org/10.5281/zenodo.24556874}
}
```

## License

All files in this repository are released under the
[Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/) license,
which is the license of the Zenodo record. See [`LICENSE`](LICENSE). Lean, mathlib, and the other
dependencies that Lake downloads during a build are not part of this repository and keep their own
licenses.
