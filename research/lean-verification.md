# First Lean milestone: zeta nonvanishing and horizontal strip

The subsequent [finite-foundation milestone](lean-finite-foundation.md)
extends the runner and extracts the pointwise reflection proof into a
mathlib-only module. The statements and archived results below describe
the first milestone.

Task: formal verification and source review. Assumptions: `UNCONDITIONAL`.
Source publication status: **PREPRINT**. The checked scope is the zeta theorem
and the six project declarations listed below, not every result in the release.

## Statements and conventions

The pinned OpenAI theorem is
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`:
for complex `s`, `7/8 < s.re` implies `riemannZeta s ≠ 0`.
Our wrapper explicitly assumes `s ≠ 1`, so its mathematical reading excludes
the pole. Mathlib defines a total complex function at the pole; the stronger
upstream formal statement uses that convention. We do not interpret it as
analytic regularity at 1.

`IsCriticalStripZero ρ` means exactly
`riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`. No assertion about enumeration,
multiplicity, simplicity, or the sign of the ordinate is hidden in this predicate.

| Project declaration | Exact role |
| --- | --- |
| `zeta_ne_zero_right` | Nonvanishing for `Re s > 7/8`, with `s ≠ 1`. |
| `reflected_zero` | A critical-strip zero gives a critical-strip zero at `1 − ρ`. |
| `zero_re_le_seven_eighths` | A critical-strip zero has `Re ρ ≤ 7/8`. |
| `zero_horizontal_strip` | `1/8 ≤ Re ρ ≤ 7/8`. |
| `zero_horizontal_displacement` | `abs(Re ρ − 1/2) ≤ 3/8`. |
| `indexed_zero_horizontal_strip` | Both bounds for each member of any indexed family of critical-strip zeros; repeated values are allowed. |

The half-plane is **open**; the resulting strip includes both endpoints.
There is no limiting parameter. Reflection uses mathlib's
`riemannZeta_one_sub`; `Re ρ > 0` excludes its nonpositive-integer exceptions,
and `Re ρ < 1` excludes its pole exception. Vanishing follows by multiplying
by `ζ(ρ)=0`, without dividing by a gamma or trigonometric factor. Reflection
changes the sign of the ordinate, which is permitted by the predicate.

Dependency chain: pinned upstream zeta theorem → right bound; mathlib functional
equation → reflected zero; right bound applied twice → closed strip → absolute
displacement and indexed-family versions. These declarations use no RH assumption.

## Reproduce

On Linux x86_64, provide Python 3.12, Git, Bash, a C toolchain for Lean's native
build, network access, and enough space for the upstream checkout and Lean caches.
Run from the repository root:

```bash
python3 -B scripts/reproduce_lean.py --fresh-project
```

The bootstrap installs pinned tools inside ignored `.tools/`, without modifying
shell configuration. `--skip-bootstrap` reuses an existing installation.
`--fresh-project` moves aside the project's `.lake/build` before checking;
dependency build caches are reused. This is a fresh **project** build, not a
claim to have rebuilt every dependency from an empty machine or clean Git commit.

The exact Lean, mathlib, OpenAI, Comparator, exporter, Landrun and Go pins are
in [lean-import-pins.json](lean-import-pins.json). The root Lake lockfile pins
the dependency graph. OpenAI is a local-path Lake requirement backed by a
bootstrap-verified Git commit: its patch hook requires all dependencies beneath
its own `lean/.lake/packages`. The root packages directory therefore uses that
layout. Upstream proof files are unchanged. Its compatibility patches modify
some dependent packages; the harness records both patch hashes and actual diffs.

Comparator is built from its pinned Lean 4.34.0 revision using the explicitly
recorded Lean 4.34.1 override, matching the upstream proof toolchain. Its exporter
revision stays pinned. The run checks the upstream challenge, builds the project,
checks all six project statements, and requires an unfinished proof to fail
specifically because of `sorryAx`. Challenge files intentionally contain `sorry`
as specifications; no solution imports them.

For this milestone the axiom report named exactly the upstream theorem and six project
theorems, with no axioms outside `propext`, `Quot.sound`, and `Classical.choice`.
Comparator reports acceptance by Lean's default kernel. Its optional external
kernel is disabled; no independent-kernel or independent-human-review claim is
made. Pair/triple regression checks are included but are not formal proofs of
those earlier manuscripts.

Every completed attempt archives logs and a manifest under
`artifacts/certificates/lean/<manifest SHA256>/`, including failed attempts.
The manifest records source hashes, exact commands and exit codes, tool versions,
binary hashes, Git state, dependency pins and compatibility diffs. Only a
`status: pass` report is successful evidence. The first successful run is
[5dabf50f…](../artifacts/certificates/lean/5dabf50f30385fc2dbb9cd4fd08b11c52bb0c7a18ce59da7a49341f2439f7db7/manifest.json):
both Comparator checks passed, the negative control was rejected, and 70 pair
plus 126 triple tests passed. This initial report predates recording actual
dependency diffs; subsequent runs include them.

The final [fresh-project run](../artifacts/certificates/lean/abeacafffc3ecb05c9cfbd592ad1dc1c33eaaaf7e4830cf76713765ce5aa6426/manifest.json)
also passed every stage, including the repeatable bootstrap, both Comparator
checks, the negative control, all seven axiom reports, and the 196 regression
tests. It records the actual dependency diffs and matches the Lean sources
and harness from that milestone. This is the evidence referenced by the QRH ledger entries.
That build retained a harmless `unnecessarySimpa` linter warning in the reflection
proof; warnings about patched dependency worktrees and intentional `sorry`
specifications are also recorded in the logs.

## What this contributes to the research

We now have a formalized, imported horizontal bound and formalized project
corollaries. This is not a new project proof of the upstream theorem. It also
does not establish RH or the remaining signed complex-argument error estimate.
In the project's scale, the new bound only gives
`abs(x_ρ) ≤ (3/8) log T` for `T > 1`. It does not make `x_ρ` tend to zero,
provide cancellation in the signed triple sum, or justify replacing the complex
test arguments by real ones. The ordinate-only target remains open.

The historical A/B proofs and their claim statuses are unchanged. The ledger's
new `QRH-` entries are outside the historical RH audits; refreshing their bound
whole-ledger hashes does not extend those audits.

## Reusable lemma shortlist

All locators below refer to the same immutable upstream commit. They are source
review candidates, not separately verified imports in this milestone.

| Candidate | Possible use and remaining work |
| --- | --- |
| `OAI.AnalyticBridge.weighted_cauchy_sq`, `DirichletL/Mellin/ExponentialSmoothing.lean` | Finite weighted complex Cauchy–Schwarz for Gram/energy bookkeeping. It uses norms of weights. Prefer the underlying mathlib inequality when that avoids a large import. |
| `OAI.AnalyticBridge.fiber_mass_bound`, same file | Group a finite sum by labels with an explicit fiber-mass bound; useful for partition bookkeeping. Does not supply the needed analytic mass bound. |
| `OAI.CubicReflectionKernel.mellin_strip_source_bound`, `DirichletL/Mellin/UniformKernelBounds.lean` | Uniform vertical decay controlled by finitely many Schwartz seminorms, for support in a fixed positive interval and real parts in a compact interval. Translate its Mellin/Fourier definitions and constants before use in our conventions. |

Primary source: OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re(s) > 7/8*, 30 September 2026, **PREPRINT**, and the associated
[formalization scope](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/003.md).
Only the zeta nonvanishing statement is imported here; the Dirichlet, Hecke,
Landau–Siegel, and later manuscript applications are outside this check.
