# Unconditional higher correlations of zeta zeros

This project studies unconditional zero correlations while retaining the
horizontal locations of the full complex zeros. The current pair baseline is
recorded as `PAIR-ASYMPTOTIC-001`, status **`proved-draft`**, in the
[theorem ledger](research/theorem-ledger.yaml).

## First formal verification milestone

The pinned OpenAI quasi-RH zeta theorem and our horizontal-strip corollaries
have passed local Lean/Comparator verification: every critical-strip zero
satisfies `1/8 ≤ Re ρ ≤ 7/8` and `abs(Re ρ − 1/2) ≤ 3/8`.
The upstream source is a **PREPRINT**. This does not settle the remaining
ordinate-only triple-correlation error.

Run `python3 -B scripts/reproduce_lean.py --fresh-project` on Linux x86_64.
See the [verification record](research/lean-verification.md) for pins, prerequisites,
checked statements, proof-checking scope, and archived evidence.

## Finite foundation formalized

The second Lean milestone verifies the five ordinate-equality patterns,
multiplicity-preserving finite regrouping, occurrence reflection, and the
eight-sign algebraic expansion. The fresh run checked **35 declarations**
in the new challenge, retained the earlier proof checks, and passed all
**196 regression tests**. See the
[finite-foundation record](research/lean-finite-foundation.md) for the exact
hypotheses and archived evidence. Infinite-sum convergence and the remaining
ordinate-only `o(1)` estimate are separate proof obligations.

## Horizontal-square inequality formalized

The third Lean milestone proves the cosh quadratic lower bound and its
finite same-ordinate consequence, preserving occurrence multiplicities
and allowing nonnegative ordinate weights. The fresh run checked **19 new
declarations**, **60 axiom reports** overall, and all **196 regression
tests**. See the [horizontal-square record](research/lean-horizontal-square.md)
for the exact inequality, proof scope, and archived evidence. The full
ordinate-only `o(1)` estimate remains open.

## Reproduce the pair baseline

Task: verification and exposition. Assumptions: `UNCONDITIONAL` for the exact
algebra. The analytic estimates are inputs from the written proof.

Install these prerequisites before running:

- Python **3.12** (standard library only), available as `python3`;
- Git and Bash;
- for a full run, `pdflatex` and `bibtex`, with the packages required by the
  manuscript: `geometry`, `amsmath`, `amssymb`, `amsthm`, `booktabs`, `hyperref`
  and their dependencies, including `etoolbox`. TeX Live 2023 was used locally.

From a fresh Git checkout, run:

```bash
./scripts/reproduce.sh
```

The command also works from another directory when invoked by its path.
It makes no downloads, installs no dependencies, and uses no previous build
artifacts. Python/TeX patch versions are recorded, not provisioned or locked.
The broader uv/Nix/container environment and CI setup are deferred.

Output goes to a unique ignored directory under `artifacts/reproduction/`.
To choose a new or empty destination, use:

```bash
./scripts/reproduce.sh --output-dir /tmp/pair-reproduction
```

Relative destinations are relative to the caller's working directory.
Inside the repository, destinations must be under `artifacts/reproduction/`.
An existing nonempty destination is rejected without overwriting it.

For a machine without TeX, explicitly request partial reproduction:

```bash
./scripts/reproduce.sh --checks-only
```

This runs all checks and generates the formulas, but its manifest reports
`status: partial` and a skipped PDF. Missing TeX in the default full mode is
an error; it is never silently skipped.

## What a run produces

| Output | Meaning |
| --- | --- |
| `pair-normalization.json` | Exact rational monomial records before/after division by `T log T`, substitution, comparison-error signs, final error scales, endpoints, source claim IDs and manuscript labels. |
| `pair-normalization.md` | Readable summary generated from those records. |
| `pair_baseline.pdf` | Manuscript built with `pdflatex`, `bibtex`, and two further `pdflatex` passes, with shell escape disabled. Full runs only. |
| `manifest.json` | Source commit and dirty state, input/output SHA256 hashes, exact Python/TeX versions, command logs, stage outcomes and test totals. |
| `logs/`, `build/` | Command output and isolated TeX intermediates, retained for diagnosis. |

The exact mathematical artifacts are deterministic. Manifest timestamps,
paths and environment records vary between runs. PDF bytes can vary across
TeX installations; each run records its actual PDF hash. The manifest excludes
its own hash and does not claim to be a computer-assisted proof certificate.

The suite currently has **70 tests**: 59 existing proof-algebra, convention and
RH-audit checks, plus 11 reproduction checks. The full command fails on any
test error, stale RH-audit record, missing source locator, failed TeX process,
unresolved citation/reference or remaining rerun request. Other TeX warnings
are recorded. Exit status is zero for a successful requested mode, including
explicit checks-only mode, and nonzero for failure. A failed run retains a
manifest and available logs once its output directory has been created.

The harness does not refresh audit hashes. Changed audited inputs must be
reviewed before updating the [RH-audit record](research/pair-rh-audit.json).
A development run is allowed and records `dirty: true`; a clean-checkout run
must record `dirty: false`. The manifest hashes new source files as well as
tracked ones, so uncommitted implementation files are identifiable.

To run only the tests, without producing a reproduction bundle:

```bash
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v
```

## Research status

**Work Package A is complete within its documented reproduction scope**
and ready to support Work Package B. The
[closure checklist](research/work-package-a-closure.md) maps all required
outputs to evidence and records the successful full clean-checkout run for
baseline revision `62a21146b1a4ea0d0d46534768ecaed7233bbe42`:
70 tests passed and the 23-page PDF built without warnings. The complete
[reproduction manifest](artifacts/work-package-a/62a21146b1a4ea0d0d46534768ecaed7233bbe42/manifest.json)
and output bundle are preserved in the repository.

The local reconstruction has a [dependency graph](research/dependency-graph.md),
[named error budget](research/pair-error-budget.md),
[Fourier/support table](research/pair-conventions.json), and
[RH-contamination review](research/pair-rh-audit.md).

The [BGSTB accepted-text comparison](research/literature-notes/bgstb-accepted-comparison.md)
is complete for the agreed Kyushu manuscript: the theorem and proof match
our baseline, with two domain/exposition issues already handled locally.
Publisher-version verification is deferred and does not block further work.

The harness implements the clean-checkout regeneration deliverable for the
current pair baseline. It regenerates normalization and error accounting from
the proved-draft analytic inputs; it does not re-prove their uniform estimates,
compute the unspecified constants, or replay external computer-assisted proofs.
Independent mathematical review, upstream foundational reconstruction and
computational replay remain nonblocking follow-ups, along with publisher-version
comparisons. Work Package A completion does not promote any claim beyond its
ledger status: the local theorem remains `proved-draft`.

Historical completion lists in the hashed audit and literature notes describe
their review date. This README and the closure checklist record the later
completion of A; those historical notes have not been changed merely to update
progress wording. The closure documentation postdates the tested baseline
revision; its proof and audited inputs are unchanged.

## Work Package B: completed smoothed weighted three-level baseline

**Work Package B is complete within its documented smoothed, weighted
full-zero scope.** The [closure review](research/work-package-b-closure.md)
maps all six required tasks to the draft theorem, dependency and assumption
records, and archived clean-checkout reproduction. The root theorem remains
**proved-draft**. Kernel removal, unweighted correlations, support enlargement
and horizontal consequences remain separate research extensions.

`TRIPLE-MASTER-001` is a **proved-draft** exact smoothed triple identity
retaining the full complex zeros. The [proof](proofs/triple_explicit_formula.tex)
and [bookkeeping tables](research/triple-master-bookkeeping.md) give the five
index-diagonal patterns, all 27 prime/archimedean/remainder terms, and the
cubic prime resonance. Convergence and smoothing dependence are explicit.
`TRIPLE-UNIFORM-001`, also **proved-draft**, supplies the
[uniform estimates and named error budget](research/triple-error-budget.md)
for all 27 terms and their 208 named remainder refinements. Bounds hold for
all `T >= 3, X,Y >= 1`, with stronger prime norm bounds when `XY <= 2T`.
`TRIPLE-LOG-GAP-001` and `TRIPLE-OFFDIAG-001` sharpen the off-diagonal
estimates. Combining them with the budget gives
`TRIPLE-SMOOTHED-ADDITIVE-001`, also **proved-draft**:

\[
\mathcal C_{3,T}(X,Y)=M_T(X,Y)
+O\!\left((1+\|\omega\|_\infty+\|\omega'\|_1)
T^{-\varepsilon}\log^4(2T+2)\right),
\]

uniformly for `T >= 3`, fixed `0 < epsilon < 1/3`,
`T^epsilon <= X,Y`, and `XY <= T^(1-epsilon)`. For fixed smoothing
this is an additive `o(1)` error, not a relative `o(M_T)` assertion.
The retained expression is defined in the budget. The subsequent
[retained-term evaluation and test-function theorem](research/triple-test-functions.md)
are recorded as `TRIPLE-RETAINED-001`, `TRIPLE-INTERIOR-VANISHING-001`, and
`TRIPLE-TEST-FUNCTION-001`, all **proved-draft**. They show the interior
observable tends to zero and prove a weighted full-zero correlation statement
for arbitrary smooth Fourier transforms compactly supported in
`xi > 0, eta > 0, xi + eta < 1`. The native kernel, multiplicities, and
complex arguments carrying horizontal zero coordinates are retained.
`TRIPLE-BOUNDARY-ESTIMATES-001` and `TRIPLE-QUADRANT-LIMIT-001`, also
**proved-draft**, give the positive-quadrant boundary limit. After division
by `log T`, integration against smooth restrictions supported in
`xi >= 0, eta >= 0, xi + eta <= 1-kappa`, for fixed `0 < kappa < 1`, tends
to an origin mass `1/4` plus density `3r/4` on each positive axis.
The [boundary budget and conventions](research/triple-test-functions.md)
include an effective error and the full-zero identity. The one-sided
inverse Fourier tests are generally not Schwartz.
`TRIPLE-SIGNED-SECTORS-001` and `TRIPLE-SIGNED-TEST-FUNCTION-001`, also
**proved-draft**, extend the native weighted correlation to Schwartz tests
with arbitrary smooth Fourier transforms compactly supported in the open
hexagon `max(|xi|,|eta|,|xi+eta|) < 1`. The normalized limit is an origin
mass `3/2` and three line contributions with coefficient `3/2` and weight
`|r|`, parameterized by `(r,0)`, `(0,r)` and `(r,-r)`, each with measure
`dr`. The [sector table](research/triple-signed-sectors.json) records the
six maps and conjugation rules. The effective error, complex zero arguments
and native kernel remain explicit.
`TRIPLE-KERNEL-PROFILE-001`, `TRIPLE-KERNEL-LOCALIZATION-001` and
`TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001`, also **proved-draft**, now give
an [explicit rational kernel profile](research/triple-kernel.md) with every
horizontal displacement retained. A summable height-localization error
justifies replacing the original kernel by this profile times the
anchor height weight, preserving the same correlation main term.
The separately evaluated critical-line microscopic profile is `3*pi/8`,
explaining the local normalization factor `3/2`; its application to all
zero tuples would require RH.
`TRIPLE-SINE-MEASURE-001` and `TRIPLE-MAIN-TERM-COMPARISON-001`, also
**proved-draft**, identify the limiting functional as exactly `3/2` times
the all-ordered sine-kernel benchmark. The
[comparison proof and partition table](research/triple-main-term-comparison.md)
include the origin, partial diagonals and ordinary-cumulant cancellation,
with the existing signed-test and localization errors retained separately.
`TRIPLE-SMOOTHED-CORRELATION-001`, **proved-draft**, assembles these results
into a [standalone unconditional smoothed three-level theorem](research/triple-theorem.md).
Its explicitly weighted full-zero observable has normalization
`16/(3T log T)` and converges additively to the all-ordered sine benchmark,
with both named errors retained. The statement includes every hypothesis,
complex argument, multiplicity convention and limit order.
Global constant-kernel replacement, an unweighted zeta correlation, and
new horizontal consequences remain separate tasks. The
[complete recorded dependency graph](research/triple-dependency-graph.md)
traces 31 claims, two provenance nodes and 58 edges, with inherited
Work Package A audit coverage identified. The
[Work Package B RH-contamination audit](research/triple-rh-audit.md) reviews
the entire triple manuscript and records no contamination found in its
reviewed scope; claims retain proved-draft status. The
[triple reproduction harness](research/triple-reproduction.md) regenerates
the exact normalization and error records, runs both suites, and builds
the manuscript. Baseline revision
`e3f5173f9703e6de263bb807d85ea7018c7a1ee0` passed full clean-checkout
reproduction; its [complete bundle](artifacts/work-package-b/e3f5173f9703e6de263bb807d85ea7018c7a1ee0/manifest.json)
is preserved in the repository. The [archive record](research/triple-reproduction.md#archived-baseline)
documents 70 pair tests, 109 triple tests and a warning-free 34-page PDF.
The [closure review](research/work-package-b-closure.md) records completion
for this baseline. Older pending-work statements in audit-bound notes
describe their review dates; the checklist and this README give the current
status without changing the mathematical or archived evidence.

### Active Work Package B extension: ordinate-only correlation

The stronger ordinate-only target is now active. The
[reduction draft](research/triple-ordinate-reduction.md) proves an exact
transfer identity and bounds both kernel errors on real test arguments:
`E_gaps=O(1/log T)` and `E_horizontal=O((log log T)^2/log T)` for fixed
Schwartz tests and smoothing. These claims have **proved-draft** status.
The complex-argument error now has an exact eight-reflection decomposition
into an even hyperbolic term and a kernel-mixing term. The latter is
**proved-draft** to vanish for fixed support `h<=s<331/4000`. On that same
support the averaged even kernel can now be replaced by `3pi/8` with an
o(1) error. The remaining kernel-free signed error `E_constant` is
**unproved** to vanish, so `ORDINATE-TRIPLE-001` remains **idea**; we do not
yet have the conventional ordinate-only asymptotic. For the original larger
support class the full signed error remains unresolved.

The seventeen extension checks supplement the historical 109 triple
checks. This extension has its own manuscript and source notes; the archived
weighted baseline and the scope of its RH audit remain as recorded.

Run the additional Work Package B regression checks with:

```bash
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py' -v
```

These exact finite checks supplement the 70-test pair suite; they are not
an analytic proof certificate. The pair reproduction harness retains its
Work Package A scope.

## Reproduce the weighted triple theorem

Use installed Python **3.12**, Git and Bash. Full runs also need `pdflatex`
and the manuscript's `geometry`, `amsmath`, `amssymb`, `amsthm`, `booktabs`,
`longtable`, `hyperref` packages and their dependencies. BibTeX is not used.
From a fresh checkout:

```bash
./scripts/reproduce_triple.sh --require-clean
```

For development, omit `--require-clean`; the manifest records the dirty
state. Use `--checks-only` for explicit partial reproduction without TeX,
and `--output-dir /tmp/triple-reproduction` for a new or empty destination.
The default is a unique ignored directory under `artifacts/reproduction/`.
Relative destinations are relative to the caller; the command also works
when invoked by path from outside the repository.

Each run writes `triple-normalization.json`, its Markdown rendering,
`manifest.json`, and logs. Full runs additionally build
`triple_explicit_formula.pdf` in three isolated passes with shell escape
disabled. Both the **70-test pair suite** and **126-test triple suite** run,
including graph and audit validation. The harness makes no downloads,
installs no dependencies, and never updates audit hashes.

See the [reproduction report](research/triple-reproduction.md) for artifact
scope, failure behavior, clean-clone evidence and reproducibility limits.
