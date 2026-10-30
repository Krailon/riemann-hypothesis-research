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

On Linux x86_64, provide Python 3.12 or newer, Git, Bash, a C toolchain for Lean's native
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

### Reuse an installed or migrated environment

After copying the complete working directory, including `.tools/` and `.lake/`, use:

```bash
python3 -B scripts/reproduce_lean.py --reuse-dependencies
```

This runs the full verification suite. It skips bootstrap, `lake update OAI`,
the PNT preparation rewrite and mathlib cache downloads. A read-only preflight
checks the upstream checkout, every locked dependency revision, all compatibility
patches from the pinned upstream tree, the prepared PNT smoothing adapter, the
tool executables and the installed pinned Lean toolchain. Missing or mismatched
inputs stop the run with a repair diagnostic; reuse mode does not fetch or patch
them. Dependency diffs are still archived. Build tools may rebuild missing or
stale compiled artifacts, so reuse mode is not a guarantee of a short or wholly
offline run.

`--skip-bootstrap` alone skips only tool installation; it still performs dependency
resolution and cache fetching. It is redundant with `--reuse-dependencies` but may
be supplied with it. `--fresh-project` remains independent: combine it with reuse
to rebuild project artifacts while keeping prepared dependencies. The existing
focused modes retain their narrower Comparator scope and also preflight their
prepared dependencies.

The `resolve` stage runs `lake update OAI`, whose hooks can download thousands of
mathlib cache files. Full verification can take hours even with prepared
dependencies. Each stage prints its command, log path and a `tail -f` command for
following progress in another terminal; output stays in that log. Completed
stages report elapsed seconds. Ctrl-C stops the stage's process group, archives
an `interrupted` manifest with the interrupted command and returns exit code 130.
This does not cover uncatchable termination such as SIGKILL or power loss.

Run `python3 -B scripts/check_lean_reproduction.py` for the runner's fast regression
tests. These mock proof-suite execution to check full/focused stage selection and
manifest outcomes, and separately test patch checks and subprocess handling;
they are not substitutes for Lean proof checking.

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

## Optimized uniform pair comparison

The [comparison milestone](lean-pair-zero-comparison.md) optimizes the zero cutoff,
handles 3<=T<5 with a fixed admissible cutoff, and uses `QRH-STRIP-001` to obtain
|L-2 pi Re Phi| <= Ct T + Cx X uniformly for T>=3 and 1<=X<=T. All constants
except the elementary absorption factor remain existential. This alternative
PREPRINT-based dependency route does not formalize the historical KV proof.

Run the new Comparator suite, combined build, complete axiom report and
regressions with `python3 -B scripts/reproduce_lean.py --reuse-dependencies
--pair-zero-comparison-only` (one shell command). Earlier Comparator suites are
not rerun by this focused mode.

## Normalized pair asymptotic

The [normalized theorem milestone](lean-pair-asymptotic.md) combines the RHS
mean square with the checked comparison, preserves the separate normalized
error scales, and proves the closed-range theorem for T>=3 and |alpha|<=1.
Finite-sum inversion supplies negative frequencies; origin and endpoint
corollaries retain their correct error scales. Total constants are existential
and the PREPRINT comparison dependency remains explicit.

Run `python3 -B scripts/reproduce_lean.py --reuse-dependencies --pair-asymptotic-only`
for the new Comparator suite, negative control, combined build, complete axiom
report and regressions. Earlier Comparator suites are not rerun in this mode.

## Pair Fourier test-function passage

The [Fourier passage milestone](lean-pair-fourier.md) completes the exact
`PAIR-TRANSLATION-001` bookkeeping and proves the integrated pair asymptotic
for compactly supported complex C¹ tests in [-1,1], with a quantitative error
budget and a Lean limit theorem. Actual complex zero differences and multiplicities
are retained. The exact branch has no strip input; the asymptotic inherits the
normalized theorem's pinned PREPRINT dependency and existential constants.

Run `python3 -B scripts/reproduce_lean.py --reuse-dependencies --pair-fourier-only`
for all 36 new Comparator statements, the negative control, combined build,
complete axiom report and regressions. Earlier Comparator suites are not rerun.

## Triple master bound, kernel identity, subseries and word expansion

The [triple master milestones](lean-triple-master.md) prove the uniform
sum of integral norms for the actual three zero terms, then discharge the
interchange and independent cutoff-limit hypotheses. The full zero-series product,
center-phase cancellation and exact smoothed K_T identity are also checked, with
absolute convergence and the exact factor 8. The five occurrence-index rows
are now separately identified, with absolute convergence, restricted interchange
and independent cutoff limits. Distinct indices need not denote distinct
complex zeros or ordinates. All signed continuous
real smoothing weights supported in [1,2] are allowed. The explicit factor
(8/3)^3 is preserved; the absolute zero-kernel constant remains existential.
The ordered 27-word explicit-formula expansion is also checked, with all four
remainders retained exactly, per-word integrability, a verified sign table and
the exact eight/nineteen split. No zero-free-strip input is used. The full
`TRIPLE-MASTER-001` remains partial. The cubic prime Fourier identity and its
absolute convergence/interchange are now checked, retaining the frequency
T log(mn/k)/(2 pi), the negative PPP sign, independent cutoffs and unnormalized
resonance mass. Nonzero resonances now have a unique common-prime/ordered-
positive-exponent parametrization, with absolutely convergent reindexing and
the exact resonant/off-resonant split. Finite-order Fourier decay is now checked
with the literal derivative L1 norm, (2*pi*|xi|)^N denominator and exact cubic
frequency substitution. The origin retains the mass bound. The master theorem
is now assembled, including X/Y symmetry, the observable norm bound and the
normalized manuscript specialization. One existential constant precedes all
weights and parameters. Only its historical numerical-effectiveness claim
remains outside formal coverage; no summed off-diagonal smallness is inferred.

Run `python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-master-only`
for all 187 triple-master Comparator statements, eleven negative controls, combined build,
complete axiom report and regressions. Earlier Comparator suites are not rerun.

The uniform triple budget is implemented in `TripleBudgetAssembly`, with its
scope and qualifications in [lean-triple-budget.md](lean-triple-budget.md).
It includes the ordered logarithmic-gap bound, convolution and diagonal
identification, all three summed off-diagonal rates, the nineteen remainder
words and the uniform additive asymptotic. Its 219 public declarations have a
separate definition-only challenge and six unfinished-proof controls. Run
`python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-budget-only`
to reproduce this milestone without rerunning earlier Comparator suites.
The effective-constant qualification and the signed complex-argument error
for an ordinate-only statistic remain separate.

## Uniform mixed-prime diagonal

The [two-scale diagonal milestone](lean-triple-mixed-diagonal.md) extends the
checked pair diagonal to every ordered pair of real scales 1<=a<=b, with a
uniform existential constant, absolute convergence, and inclusive endpoints.
Its 28 public statements and three unfinished-proof controls have a focused
reproduction mode:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-mixed-diagonal-only
```

This covers only the mixed-diagonal part of `TRIPLE-RETAINED-001`.

## Sharp first smoothing moment

The [first-moment milestone](lean-triple-smoothing.md) proves the bounded
logarithmic smoothing mean, exact integrable correction, the uniform explicit
bound 0<=J1-log T-mu<=2/T, and the fixed-weight limit. It includes T=3 and
requires no arithmetic or zero-location input.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-smoothing-only
```

The focused suite compares all 13 public declarations and rejects two
unfinished-proof controls. Resonance decay and the assembled retained-term
evaluation remain separate tasks.

## Decaying resonance bound

The [resonance decay milestone](lean-triple-resonance-decay.md) proves the
square-root proper-power count without logarithmic loss, an absolutely
summable dyadic cover, and the uniform bound
0<=R_res(X,Y)<=C_res log(2XY)^3/sqrt(XY) with an explicit convergent-series
constant. It includes either unit scale, product one and repeated prime factors.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-resonance-decay-only
```

The focused suite compares all 32 public declarations and rejects three
unfinished-proof controls. The full retained-term evaluation remains a
separate assembly step.

## Full retained-term evaluation

The [retained-term assembly](lean-triple-retained.md) gives the exact formula,
named diagonal and smoothing error bounds, resonance decay, and a combined
additive estimate, with symmetry and endpoint checks. The diagonal constant
remains existential; the other constants are explicit.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-retained-only
```

The focused suite compares all 28 public statements and rejects three
unfinished-proof controls. Interior vanishing remains a separate milestone.

## Interior-vanishing corollary

The next focused suite checks the retained O(T^(-epsilon)L^3) bound,
the full-observable O((1+W+W1)T^(-epsilon)L^4) bound, and both uniform
moving-range limits. It includes 21 independently compared declarations,
three unfinished-proof controls, inclusive height and scale endpoints,
and exchange symmetry. Absolute constants remain existential. See
[the proof scope](lean-triple-interior-vanishing.md) and
[the inventory](lean-triple-interior-vanishing-inventory.json).

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-interior-vanishing-only
```

This retains the full-zero observable and does not close the signed
complex-argument error for an ordinate-only statistic.

## Interior weighted test-function passage

The focused suite checks support margins, joint entire regularity, Schwartz
Fourier inversion, the absolute frequency/zero interchange, the exact native
kernel identity, local-spacing bounds and fixed-test limits. All 31 public
statements have independent specifications and four unfinished-proof controls.
The combined build, complete axiom audit and regressions are included:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-test-function-only
```

See [the proof scope](lean-triple-test-function.md) and
[the declaration inventory](lean-triple-test-function-inventory.json).
Constants remain existential, and the ordinate-only signed error remains open.


## Frequency axes and origin

The completed boundary suite checks all 143 public declarations across 51
modules: exact full-zero and tempered Fourier passage, the uniform integrated
budget, local origin and both axis profiles, and the normalized quadrant limit.
Six unfinished-proof controls, the combined build and complete axiom report
are included:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-boundary-only
```

See [the certified scope and manifest](lean-triple-boundary.md) and
[the declaration inventory](lean-triple-boundary-inventory.json). The axes and
origin are included; the upper support margin remains strictly positive.
Inherited constants remain existential. Signed-sector assembly is completed
by the following milestone; the ordinate-only signed error remains open.


## Signed frequency sectors and smooth tests

The completed signed-sector suite checks 84 public statements across 19 modules:
positive-base convergence, reciprocal reflection, all six sectors and null seams,
the sharp hexagonal majorant, the exact full-zero identity, complex test
pullbacks, entire/Schwartz inversion and the uniform normalized asymptotic.
The final origin and line coefficients are 3/2, with parameter measure dr on
all three lines and no additional half weights.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-signed-sectors-only
```

See [the certified scope and manifest](lean-triple-signed-sectors.md) and
[the declaration inventory](lean-triple-signed-sectors-inventory.json).
The support stays strictly inside the hexagon. Constants remain existential;
the horizontal kernel and complex test arguments are retained. This completes
the mathematical signed-sector passage, with historical effectiveness claims
kept separate, and does not resolve the ordinate-only signed error.
