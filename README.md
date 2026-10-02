# Unconditional higher correlations of zeta zeros

This project studies unconditional zero correlations while retaining the
horizontal locations of the full complex zeros. The current pair baseline is
recorded as `PAIR-ASYMPTOTIC-001`, status **`proved-draft`**, in the
[theorem ledger](research/theorem-ledger.yaml).

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

## Work Package B: an interior weighted test-function theorem

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
The next step is analysis near the frequency axes and origin. The general
Work Package B theorem and a new horizontal consequence remain targets.

Run the additional Work Package B regression checks with:

```bash
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py' -v
```

These exact finite checks supplement the 70-test pair suite; they are not
an analytic proof certificate. The pair reproduction harness retains its
Work Package A scope.
