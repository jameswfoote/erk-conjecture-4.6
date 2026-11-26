# ERK Conjecture 4.6

**A proof of bistability at all processivity levels in a model of ERK regulation**  
James Foote · University of British Columbia · 26 November 2026

The manuscript proves that for each prescribed pair of kinase and phosphatase processivities in the open unit square, a single choice of thirteen positive rates and three positive totals supports two distinct positive equilibria. Both are exponentially stable on the same nine-dimensional stoichiometric class.

OpenAI Codex sessions developed and formalized the proof, checked the finite example, and reviewed the work internally.

## Package contents

| File | Contents and provenance |
| --- | --- |
| `ERK-Conjecture-4.6.pdf` | Byte-for-byte copy of the final five-page manuscript. |
| `lean-proof.zip` | The standalone `proof/` directory from the manuscript’s source supplement. It contains all 17 Lean modules, the toolchain pin, Lake configuration, pinned dependency manifest, mathlib import list, replay script, and original transcript. |
| `sage-certificate.zip` | The original `prescribed-cubic-finite.py` for the exact unequal-processivity example in Table 1. |
| `verification-transcript.txt` | Original Lean build output, theorem statements, and axiom inspection. This is identical to `proof/replay.txt` in the Lean archive. |
| `independent_erk_verification.py` | A byte-identical copy of the lab’s additional checker, originally `verification/check_finite_saturation.py`. It checks the low- and high-saturation controls at a different prescribed pair. |
| `independent_erk_verification_results.txt` | Standard output captured by running that additional checker with SageMath 10.10 for this package. |

The last two filenames are distribution names. The download labels supplied with the package request had no source URLs. The files provided here come from the lab checker identified above and its replay.

## Reproduce the Lean proof

Use a POSIX shell, Git, unzip, and the Lean toolchain manager **elan**. Start in the folder containing this README. The first cache retrieval needs network access on a fresh installation.

```sh
unzip lean-proof.zip
cd proof
xargs lake exe cache get < mathlib-imports.txt
lake env sh replay.sh > ../local-lean-transcript.txt
cd ..
tail -n 2 local-lean-transcript.txt
```

The replay compiles each project module in a fresh temporary directory. It then imports the top-level proof, checks its type against `ERK.Target.Conjecture46`, and prints its axioms. The expected last two lines are

```text
'ERK.conjecture_4_6' depends on axioms: [propext, Classical.choice, Quot.sound]
Checked all 17 project modules.
```

The pinned toolchain is Lean 4.25.2 (commit `b86e2e5824bcdbfa0e8d02dd97b4c48792a385d1`) and mathlib is pinned to `c98ae54af00eaefe79c51b2b278361ca94e59bfb`. The archived transcript was recorded on Apple Silicon. A different host may print a different platform string on its Lean version line. The main theorem is in `proof/Bistability.lean`. The source comparison with the published equations is in `proof/Source.lean`.

## Reproduce Table 1

With SageMath 10.10 installed, run these commands in the package folder with Python assertions enabled (the Sage default).

```sh
unzip sage-certificate.zip
sage -python prescribed-cubic-finite.py
```

The certificate uses the exact rational inputs `p = 1/2`, `q = 2/3`, `K = 1024`, and `delta = eta = 1/1000000`. It checks the equilibrium equations, totals, and physical-time stability. In order of increasing free S01 concentration, it reports **0, 0, 1** eigenvalues in the open right half-plane. The concentrations printed for display are approximations to exact real algebraic values.

## Reproduce the additional checks

Run the separate script with SageMath 10.10 from the package folder.

```sh
sage -python independent_erk_verification.py > local-additional-results.txt
diff -u independent_erk_verification_results.txt local-additional-results.txt
```

Here `p = 999/1000`, `q = 9999/10000`, and `delta = eta = 10^-12`. At `K = 1` there is one positive equilibrium with zero unstable directions. At `K = 1048576` the three positive equilibria have **0, 1, 0** unstable directions in order of increasing free S11. These two controls and Table 1 give finite examples. The all-pairs statement is established by the Lean theorem.

## Source revisions and file integrity

- Manuscript revision: `cdc4d52235248cd69a46d6beefb10f2609eb1831`.
- Frozen Lean proof: `a3f3960572a11567213658facf04435084aa6eca`.
- Original Table 1 certificate: `d3b22f63ac1df7d3b6d4e41892ee447066bc8e42`.
- Additional saturation checker: `1a69a6c5013c8807a1007c46738d036c5a0dfcec`.

SHA-256 digests for the six payloads follow. Archive digests refer to the split ZIPs included here.

```text
0a8ccfc7e4e4434d275b4213a69a8839bec0ce3bec12d514c399ae8c5dc265fc  ERK-Conjecture-4.6.pdf
55d808d50e3a939fe7b9a82f6d66fa81056c9edb384c75278717a088544b1d78  lean-proof.zip
272fa95405e90c12e213f2e948e41ca6a137338463e169ede85c7685aa961e98  sage-certificate.zip
8c052a3141fc812d266bb372f14a38d81bff74299aff30b2966654f12871ae21  verification-transcript.txt
9990308f0cb7d962bc9c2c873376b5a8550624221a5e121fa06bd6e228c1df4f  independent_erk_verification.py
3241ed50f28be43102207702b8f818a44f52d0b14819a063b979e94d14988620  independent_erk_verification_results.txt
```
