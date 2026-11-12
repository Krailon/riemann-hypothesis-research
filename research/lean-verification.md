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

### Parallel rejection controls

The runner defaults to `--control-jobs 4`, capped by the process's CPU affinity.
Use `--control-jobs 1` for the original serial ordering, or explicitly choose a
larger positive value on machines with sufficient memory:

```bash
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only --control-jobs 4
```

Parallel mode queues the selected unfinished-proof controls, completes the
positive checks, and prebuilds the controls' challenge and solution modules.
A bounded worker pool then runs those controls before the final combined build
and axiom audit. Each worker has copied project sources/configuration and its own
`.lake/build`, seeded with `cp --reflink=auto` (ordinary copies when cloning is
unavailable). No writable hardlinks are used. Prepared dependency trees are
shared through symlinks; Comparator's unchanged Landrun sandbox permits build
writes only inside the worker's own `.lake`, so the dependency targets remain
read-only to those builds. Bootstrap, dependency preparation, positive checks,
final build, axiom audit and regression suites remain sequential stages. Lake
may use its own internal parallelism within a build.

Worker scratch trees live under `.lake/rejection-controls-*`, outside archived
logs, and are removed after worker processes terminate. A conservative free-space
check reserves the full ordinary-copy size per worker plus 1 GiB. Memory is not
reserved: reduce the worker count if the host lacks RAM. As with serial mode,
catchable interruption archives an incomplete run; SIGKILL/power loss may leave
scratch directories behind.

Every original control and JSON configuration remains selected. A control passes
only when Comparator exits nonzero and its log contains
`Illegal axiom detected: 'sorryAx'`. Unexpected success or another failure cause
stops the pool, cancels queued controls and terminates active process groups.
The manifest (schema version 2) retains deterministic command declaration order;
actual start/end timestamps show execution order. It records worker assignments,
requested/effective concurrency, setup/execution elapsed time and sampled Linux
process-group RSS. RSS is sampled every 0.5 seconds, can double-count shared pages
and is not a rigorous upper bound on peak memory. Per-control logs keep their
existing names. `--control-jobs 1` avoids worker copies and uses the original
per-stage execution path.

Fast checks: `python3 -B scripts/check_lean_reproduction.py` tests scope and
archival behavior; `python3 -B scripts/check_lean_control_pool.py` uses real small
subprocesses to test overlap, isolation, rejection criteria, cancellation,
process-group interruption and scratch cleanup. These are harness tests, not
mathematical proof certificates.

The [localization benchmark](lean-rejection-control-benchmark.md) records a
43.5-to-16.1-minute improvement with four workers on the current host. Eight
workers were not benchmarked because their projected memory demand exceeds its RAM.

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


## Exact kernel-localization identity

The first localization stage is complete: 14 checked public declarations give
the anchor translation, integrability of both weighted profile terms, absolute
error-integral convergence and the exact decomposition in master and test
order. The named error is an explicit weight-difference integral. The outside
factor is 1/T, and the conjugated anchor's horizontal sign is retained.
The hypotheses are continuity, support in [1,2] and T>0.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only
```

See [the certified scope and manifest](lean-triple-kernel-localization.md) and
[the declaration inventory](lean-triple-kernel-localization-inventory.json).
TRIPLE-KERNEL-LOCALIZATION-001 remains partially formalized. Its quantitative
tuplewise estimate, separate summed near/far bounds, profile correlation transfer
and height limit are subsequent stages; no ordinate-only conclusion is added.

### Quantitative tuplewise kernel localization

The localization suite now includes the sharp half-strip scalar bound, the
exact two-center majorant integral through coincident centers, Lipschitz
error-integral convergence and the uniform 64pi/27 tuplewise bound. A derivative
bound supplies the manuscript smoothing constant. Master and test orderings
and equal-ordinate tuples are covered. This extends the fixed-tuple stage;
summed near/far estimates and profile transfer remain separate.

The focused command remains:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only
```

The extended suite checks 28 statements and four unfinished-proof rejection
controls, then the combined project build, complete axiom report, coverage,
harness and pair/triple regressions. See
[the localization record](lean-triple-kernel-localization.md) for scope and
certificates.

### Summed near/far kernel localization

The localization suite now includes the disjoint three-region partition,
separate uniform near/far integral-norm budgets, absolute summability of the
kernel error and its derivative-bound wrapper. It checks 71 public statements
in 13 modules and nine unfinished-proof rejection controls, together with the
combined build, axiom audit and regressions. The command remains
`python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only`.
See [the localization record](lean-triple-kernel-localization.md) for the bounds,
endpoint conventions, finite-cutoff proof route and certificate. Constants of
the summed estimates remain absolute existential constants. Complex-test
profile transfer and height limits remain separate.

### Unweighted frozen-profile summability

The localization suite includes the directly defined frozen coefficient in
master and test order, absolute summability with uniform mass bounds, the
summed localization identity and independent occurrence cutoff convergence at
fixed height. Its 88 statements in 16 modules are covered by independent
expected statements and twelve unfinished-proof controls. The focused command
remains `python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only`.
See [the localization record](lean-triple-kernel-localization.md) for scope and
certificate. Complex-test weighting and transfer, T-to-infinity limits and
numerical evaluation of the inherited constants remain separate.


### Complex-test weighted summability

The localization suite extends the signed coefficient majorant to the full
complex Fourier test and transfers absolute summability and uniform mass
bounds to the test-weighted kernel, frozen profile and localization error.
Independent finite and inclusive ordinate cutoffs converge for the weighted
frozen series at fixed T. Its 101 statements in 18 modules have independent
expected contracts and sixteen unfinished-proof rejection controls. Run
`python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only`.
See [the localization record](lean-triple-kernel-localization.md) for exact
hypotheses and verification evidence. Normalized correlation transfer and
T-to-infinity limits remain the next step; horizontal information is retained.


### Normalized profile transfer and fixed-test height limit

The localization suite now includes the exact normalized profile formula,
the absolutely convergent transfer-error identity, raw and simplified uniform
transfer estimates, a derivative-bound wrapper, and normalized independent
finite/inclusive ordinate cutoffs. The inherited signed error and transfer
error remain separate in the combined uniform bound. The fixed positive-margin
limit and compact-support-in-the-open-hexagon corollary recover signedLimit.
The suite checks 121 statements in 22 modules with nineteen unfinished-proof
controls; run the existing focused command with `--reuse-dependencies`.
See [the localization record](lean-triple-kernel-localization.md) for the
certificate and exact scope. Historical coverage stays partial solely for the
uncertified numerical-effectiveness qualification. The ordinate-only signed
error is not resolved by profile localization.


### Effective uniform microscopic profile

The localization suite adds an explicit gap bound and scaled-gap rate with
C_R=16 pi R(R+1)/9, including the closed horizontal cube. The height threshold
T>=2 pi exp(2 pi) ensures L_T>=1, and the profile converges uniformly on the
full five-parameter box to its horizontally dependent zero-gap profile.
Zero radius, coincident/zero gaps and horizontal endpoints are checked.
The suite covers 137 statements in 26 modules with twenty-two unfinished-proof
controls. Use the existing localization reproduction command with dependency
reuse. See [the localization record](lean-triple-kernel-localization.md) for
verification evidence and scope. The critical-line quadratic expansion and
summed constant-kernel replacement remain separate; the new explicit constant
does not resolve effectiveness of inherited counting constants.


## Critical-line quadratic profile and tuplewise kernel specialization

The localization suite extends to 160 public statements in 29 modules, with
26 unfinished-proof controls. It includes the explicit fourth-order remainder,
the height specialization, and quadratic-corrected and leading-only tuplewise
kernel estimates in master and test order. Every tuple theorem assumes zero
horizontal displacement for its three occurrences explicitly. Effective constants
are C_R=pi(R^4+R^6+R^8), B_R=15pi R^2/32+C_R and localization coefficient 16pi/27.
Details and verification provenance are recorded in
[the localization note](lean-triple-kernel-localization.md).
Use the existing focused localization command; four rejection workers remain the
default. This stage does not replace kernels inside an unrestricted infinite sum.

## Explicit zero-gap horizontal profile

The localization suite extends to 181 public statements in 31 modules and
29 unfinished-proof controls. The exact zero-gap profile retains all three
horizontal parameters, with each denominator factor in [3,4] and their product
in [27,64] throughout the closed cube. Positivity, symmetry, all eight corners,
the cancelling/aligned one-parameter families and the nonconstant quarter-point
example are checked. The scaled-gap bound and uniform microscopic limit now
identify their explicit horizontal target. This adds no zero-sum interchange
or global critical-line assumption. See the
[localization note](lean-triple-kernel-localization.md) for statements and provenance.

## Local critical-line normalization

The localization suite extends to 194 statements in 33 modules and 32 rejection
controls. The local identity (8/(T log T))(3pi/8)=c(T)/(T L_T) is checked for
T>2pi, with c(T)=3 log(T/(2pi))/(2 log T). Real and complex versions, bridges to
the existing transfer normalization, the exact logarithmic error and the limit
c(T)->3/2 are included. The excluded endpoint T=2pi is explicitly checked.

This completes formal coverage of TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001
through its checked components, while retaining its historical ledger status.
The main-term comparison and ordinate-only research claims remain separate.
Statements and provenance are in the [localization note](lean-triple-kernel-localization.md).

## Sine-cycle interval geometry

A separate sine-measure suite checks 20 public statements in two modules,
with six unfinished-proof rejection controls. It proves the exact closed
interval overlap and Lebesgue measure, finite integrability and the product
indicator integral, including the singleton boundary and all six sectors.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-sine-measure-only
```

The default four-worker control pool, combined build and full axiom report
remain enabled. This supplies partial coverage of TRIPLE-SINE-MEASURE-001;
the sinc Fourier pairing and full five-partition benchmark remain separate.
See the [sine-measure note](lean-triple-sine-measure.md).

## Sinc Fourier pairing

The sine-measure suite now covers 49 public statements in eight modules,
with twelve rejection controls. It includes the compact parameter majorant,
justified Fubini, pointwise inverse transform of the hexagonal density,
unrestricted bilinear Schwartz pairings for the cycle and squared sinc,
weighted absolute convergence and unit density mass. Existing FourierPlane,
pairMeanSinc and pairMeanTriangle conventions are reused.

Use the same `--reuse-dependencies --triple-sine-measure-only` command.
TRIPLE-SINE-MEASURE-001 remains partial: the five-partition benchmark and
cumulant assembly are subsequent work. See the
[sine-measure note](lean-triple-sine-measure.md) for the exact scope.

## Five-partition sine benchmark and cumulants

The sine-measure suite now checks 125 statements in 20 modules, with 22
unfinished-proof controls. The exact five partition Fourier table, tempered
realizations, moment-cumulant identity, distinct ordinary/factorial formulas,
and closed-hexagon cancellation complete formal coverage of
TRIPLE-SINE-MEASURE-001. Its historical ledger status remains unchanged.

Use `--reuse-dependencies --triple-sine-measure-only`. The main-term comparison
and zeta support-boundary extension remain separate. Details are in the
[sine-measure note](lean-triple-sine-measure.md).

## Exact and weighted main-term comparison

The dedicated `--triple-main-term-comparison-only` suite checks 29 statements
in five modules and eight unfinished-proof rejection controls. It connects the
positive-inverse compact Fourier test to the five-partition sine benchmark,
proves reflection and closed-hexagon cancellation without test symmetry, and
rewrites the signed and frozen weighted bounds with main term (3/2) S3[F].
Both fixed-margin and compact-interior limits, including normalization by 2/3,
are checked. The earlier local factor 3b/(2 log T) is unchanged. The coverage
of `TRIPLE-MAIN-TERM-COMPARISON-001` remains partial because numerical
effectiveness of inherited existential uniform constants is not certified.
See [the comparison record](lean-triple-main-term-comparison.md).

## Unit-normalized smoothed triple theorem

The `--triple-smoothed-correlation-only` suite checks 20 public statements
in four modules and nine rejection controls. It assembles the exact normalized
profile sum, raw absolute convergence, independent cutoffs, supremum-norm
uniform additive bound, fixed-test limits and general-filter varying-family
error limit. The two named envelopes remain explicit. Uniform constants retain
their inherited existential status, so historical claim coverage remains
partial for effectiveness. See [the formalization record](lean-triple-smoothed-correlation.md).

## Constant-kernel replacement

The `--constant-kernel-only` suite now checks 68 public statements in 14
modules and 17 rejection controls. It extends the pointwise eight-reflection
bound with project scaling, uniform quadratic P24 Fourier decay, fixed-height
absolute convergence, all three independent cutoff limits, the exact even-
error split and the normalized summed moment estimate. Constants are explicit
and conservative; Fourier integrals are evaluated before summing over zeros.
Density-based replacement vanishing and the unaveraged constant-term
identification remain separate, as does the open kernel-free signed error.
See [the formalization record](lean-constant-kernel.md).

## Density-count and conditional window milestone

The density adapter suite defines actual multiplicity-counted right, left and
two-sided tails in half-open and closed height windows. It checks endpoint and
reflection identities and the uniform comparable-window/scaled-tail consequences
**under the explicit `UniformDyadicDensity C T₀` hypothesis**. The density theorem
itself is not proved or imported as an axiom. The 35 statement contracts, 11
rejection controls and complete axiom audit are available through
`python3 scripts/reproduce_lean.py --reuse-dependencies --density-adapters-only`;
they are also part of the default harness. See [the scope and conventions](lean-density-adapters.md).
The analytic density input, close-pair estimate, density-based moment/vanishing
argument and open signed complex-argument error remain separate obligations.

## Littlewood rectangle-counting milestone

The exact Littlewood identity and horizontal count bound are formalized using
Zeta23's weighted argument principle. The proof constructs compatible boundary
logarithms, verifies derivatives and integrability, preserves analytic
multiplicity, and identifies the count with actual zeta occurrences. It requires
nonvanishing on the entire rectangle boundary. The 36 contracts and 11 rejection
controls run through `--littlewood-only` and the default reproduction harness;
see [conventions and scope](lean-littlewood.md). Boundary-zero limits, mollifier
estimates and the uniform analytic density theorem remain separate obligations.


## Mollified Littlewood extension

The Littlewood suite now includes 20 further statements proving finite analytic
orders on the rectangle, exact product-order and strict-count additivity, and the
actual zeta count bound from a boundary budget for zeta*M. Shared and additional
mollifier zeros retain all multiplicities. M needs analyticity near the rectangle
and the product must be nonzero on its border; interior nonvanishing is not
assumed. The extended `--littlewood-only` suite has 56 contracts, 16 rejection
controls and ten modules. Boundary-zero limits and analytic mean-square/density
estimates remain unformalized; see [the precise scope](lean-littlewood.md).

## Approximate functional equation work in progress

The 141-statement AFE prerequisite suite includes inclusive-cutoff algebra,
reflection valid at zeta zeros, moving-cutoff integrability, compact-height
bounds, explicit contour-denominator separation, a proved complex Stirling
identity, the uniform chi-phase estimate, phase-error transfer in both
cutoff orders, absolute Mellin interchange, and the fixed-radius Hankel identity
for every nonreal parameter. The latter includes paired residue normalization,
shrinking-circle control and analytic continuation on both half-planes. See `lean-approximate-functional.md` for exact domains and the
proof dependency order. The global sharp two-sum contour identity and its
large-height remainder estimate are still unproved. No analytic density
theorem is claimed. The focused reproduction is
`--reuse-dependencies --approximate-functional-only --control-jobs 8`; it uses
23 rejection controls and also runs the combined build and full axiom audit.
