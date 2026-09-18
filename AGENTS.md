# AGENTS.md

## Project title

**Unconditional Higher Correlations of Riemann Zeta Zeros and Horizontal Zero Information**

## Mission

Develop **unconditional three-level and higher correlation formulae for the nontrivial zeros of the Riemann zeta function without presupposing the Riemann Hypothesis (RH)**, and determine rigorously how much those correlations constrain the horizontal locations of the zeros.

The project has two coupled goals:

1. Extend unconditional pair-correlation methods to genuine 3-level and, where feasible, n-level statistics.
2. Convert the resulting statistics into quantitative information about
   \[
   \beta-\tfrac12,\qquad \rho=\beta+i\gamma,
   \]
   such as lower bounds for the proportion of zeros on the critical line, upper bounds for moments of horizontal displacement, exclusion of classes of hypothetical off-line configurations, or structural restrictions on any exceptional set.

This is a **theoretical analytic-number-theory project**. Computation is used to discover, falsify, optimize, and certify finite or numerical subclaims; it is never a substitute for proof of an asymptotic theorem.

---

## 1. Research stance

### 1.1 What counts as progress

High-value outcomes include any of the following:

- a correct unconditional 3-level correlation theorem in a nontrivial Fourier-support region;
- a higher-correlation identity or inequality that remains valid with zeros off the critical line;
- a demonstrable enlargement of the support region available to an existing unconditional correlation theorem;
- a rigorous implication from 3-level/higher correlation information to a stronger lower bound for the proportion of critical-line zeros;
- a rigorous bound on moments or tails of
  \[
  (\beta-\tfrac12)\log T;
  \]
- a theorem showing that a specified collection of correlation information rules out a specified family of off-line zero configurations;
- a sharp “barrier theorem” proving that a given pair-correlation or kernel method cannot exceed some critical-line proportion without genuinely new input;
- a reusable explicit-formula or positivity framework that makes higher-level horizontal-information arguments systematic.

A smaller but still publishable result may be an exact optimization theorem, a new extremal kernel, a nontrivial conditional-to-unconditional reduction, a new finite-dimensional positivity inequality, or a rigorous computation that closes a well-defined analytic subproblem.

### 1.2 What does **not** count as theorem-level progress

Do not present any of the following as progress toward proving RH unless a precise mathematical implication is established:

- plots of zeros on the critical line;
- agreement with GUE/random-matrix predictions;
- numerical evaluation of a correlation statistic at finite height;
- optimization output without a rigorous certificate;
- symbolic manipulation without justified interchange of limits/sums/integrals;
- a result that silently assumes RH, GRH, simplicity, or that all zeros being summed are on the line;
- a statement that holds for “100% of zeros” in density but does not exclude an exceptional set.

---

## 2. Core mathematical objects and conventions

Freeze conventions at project start. Any paper or notebook using a different convention must translate explicitly.

### 2.1 Zeros

Write nontrivial zeros of \(\zeta(s)\) as
\[
\rho=\beta+i\gamma,
\]
counted with multiplicity unless explicitly stated otherwise.

The functional equation and conjugation give the standard symmetries
\[
\rho\mapsto 1-\rho,\qquad \rho\mapsto \bar\rho.
\]
Any synthetic or hypothetical off-line configuration used in experiments must respect these symmetries.

Never replace \(\rho\) by \(\tfrac12+i\gamma\) in an “unconditional” derivation unless that replacement is itself justified for the term at hand.

### 2.2 Scaling

Near height \(T\), use the local mean-spacing scale
\[
L_T:=\frac{\log(T/2\pi)}{2\pi}.
\]
For vertical differences define, as appropriate,
\[
u_j=L_T(\gamma_j-\gamma_1).
\]
For horizontal displacement use
\[
x_\rho=(\beta-\tfrac12)\log T
\]
or a locally normalized version with \(\log(|\gamma|+2)\). State which normalization is used.

### 2.3 Correlation observables

Do not force higher correlations into a form that already assumes RH. A generic 3-level statistic should retain the full zeros:
\[
\mathcal R_{3,T}[F,W]
=
\sum_{\rho_1,\rho_2,\rho_3}
W_T(\rho_1,\rho_2,\rho_3)
F\!\left(
L_T(\gamma_2-\gamma_1),
L_T(\gamma_3-\gamma_1)
\right),
\]
where \(W_T\) may include horizontal weights depending on the \(\beta_j\), a smooth height cutoff, and diagonal-exclusion factors.

A more informative family is
\[
\mathcal R_{3,T}[F;H]
=
\sum_{\rho_1,\rho_2,\rho_3}
w_T(\gamma_1,\gamma_2,\gamma_3)
F(\mathbf u)
H(x_{\rho_1},x_{\rho_2},x_{\rho_3}),
\]
with \(H\equiv1\) recovering a purely vertical statistic. One central research question is which choices of \(H\), or which implicit horizontal weights arising naturally from the explicit formula, can be controlled unconditionally.

### 2.4 Fourier transform

Use throughout
\[
\widehat f(\xi)=\int_{\mathbb R}f(x)e^{-2\pi i x\xi}\,dx,
\qquad
f(x)=\int_{\mathbb R}\widehat f(\xi)e^{2\pi i x\xi}\,d\xi.
\]

For \(\mathbb R^d\), use the corresponding dot-product convention. Every support condition must be stated in these units.

### 2.5 Diagonals and multiplicity

Every correlation sum must specify whether tuples with equal zeros are included, whether equality means equal ordinates or equal complex zeros, and how multiplicity is counted.

Maintain separate notation for:

- all ordered tuples;
- distinct complex zeros;
- distinct ordinates;
- tuples with pairwise distinct indices;
- diagonal and partial-diagonal contributions.

At 3-level and above, partial diagonals are not bookkeeping trivia; they can carry main terms.

---

## 3. Primary research program

### Work Package A — Rebuild the unconditional pair-correlation baseline

Before attempting 3-level correlation, reproduce the relevant unconditional pair-correlation theorem from first principles in project notation.

Required outputs:

1. A dependency graph of every analytic input.
2. A version in which every appearance of \(\beta\) is visible.
3. A decomposition into diagonal, prime/prime-power, archimedean, and error terms.
4. Uniform versions of every estimate needed later.
5. A machine-checkable table of Fourier conventions and support restrictions.
6. A “RH contamination audit”: a line-by-line check that no step imports a theorem whose stated version assumes RH.

The reproduction is complete only when the main term and error term can be regenerated from a clean checkout by a scripted symbolic/numerical test suite where applicable.

### Work Package B — Derive an unconditional 3-level explicit formula

Start from smoothed sums. Avoid sharp height cutoffs until the final Tauberian/desmoothing stage.

Target a theorem of the schematic form
\[
\mathcal R_{3,T}[F]
=
\mathcal M_{3,T}[F]
+
\mathcal E_{3,T}[F],
\]
for a nonempty class of Schwartz test functions \(F\) whose Fourier transforms satisfy an explicit support restriction.

Do **not** prejudge the optimal support region. Treat the support polytope as an object to derive from the prime-side combinatorics and available mean-value bounds.

Tasks:

- derive the triple explicit-formula expansion without substituting \(\beta=1/2\);
- classify diagonal, semi-diagonal, and genuinely off-diagonal terms;
- identify which terms are controlled by PNT-level input, which require prime-pair/triple information, and which can be bounded by mean-value theorems;
- isolate exactly where limited Fourier support kills hard off-diagonal configurations;
- preserve uniformity in all auxiliary smoothing parameters;
- derive an error budget with each source of loss separately named.

The first acceptable theorem may have a very small support region. Correct unconditional structure is more important than an aggressive region.

### Work Package C — Move to n-level structure

Once 3-level is stable, abstract the combinatorics before computing 4-level by hand.

Build a partition-based formalism for coincidences among \(n\) zero indices and for the corresponding prime-side terms. Seek a general statement parameterized by set partitions, matchings, or cumulants.

Investigate cumulants as an alternative to raw moments/correlations. Higher cumulants may isolate genuinely new information while automatically removing lower-order diagonal structure.

Questions:

- Which n-level terms are determined entirely by lower-level correlations?
- What is the first genuinely new off-diagonal arithmetic input at each level?
- Does a cumulant formulation enlarge usable support or simplify horizontal sensitivity?
- Is there a hierarchy of positivity constraints analogous to moment matrices?

### Work Package D — Extract horizontal information

This is not an afterthought; design the correlation theorem with the extraction step in mind.

Develop at least three parallel mechanisms.

#### D1. Positive-semidefinite / Gram-matrix method

Construct finite or Hilbert-space Gram forms from test functions evaluated at zeros. Use
\[
\langle v_i,v_j\rangle
\]
and higher tensor analogues to convert correlation identities into positivity inequalities.

Study moment matrices involving weights such as
\[
e^{a(\beta-1/2)},\quad
\cosh(a(\beta-1/2)),\quad
(\beta-1/2)^{2k},
\]
chosen so functional-equation symmetry is respected.

Determine whether 3-level information supplies PSD constraints unavailable from second moments.

#### D2. Weil explicit-formula positivity

Recast candidate correlation functionals in a form compatible with Weil's Hermitian form. Track exactly which positivity statements are unconditional and which would be equivalent to RH.

The goal is not to smuggle in Weil positivity. The goal is to discover **restricted positive forms** whose positivity follows from elementary Hilbert-space or finite-dimensional arguments and whose explicit-formula expansion penalizes horizontal displacement.

#### D3. Extremal-kernel optimization

For a proven correlation identity, formulate the best critical-line or horizontal-moment consequence as an extremal problem over admissible kernels.

Typical structure:
\[
\text{maximize/minimize } \mathcal L(K)
\quad\text{subject to}\quad
\widehat K\text{ supported in }\Omega,
\quad K\ge0\text{ or PSD constraints},
\quad \mathcal N(K)=1.
\]

Use numerical optimization only to discover candidates. Convert the final candidate into an exact or interval-certified object before it enters a theorem.

### Work Package E — Barrier theorems

For every successful extraction framework, ask the dual question:

> Given exactly the correlation identities and positivity constraints currently available, what is the strongest possible conclusion about the horizontal distribution?

Formulate the problem as a linear, semidefinite, or moment optimization problem when possible. A certified dual solution proving that the method cannot exceed a particular bound is a publishable negative result and a guide to what new input is necessary.

### Work Package F — Generalization to L-functions

Do this only after the zeta case is stable.

Natural next objects:

1. primitive Dirichlet \(L\)-functions;
2. a family of automorphic \(L\)-functions with controlled analytic conductor;
3. Rankin–Selberg \(L\)-functions where an explicit formula and suitable coefficient mean values are available.

The purpose is diagnostic: determine which parts of the higher-correlation/horizontal-information mechanism are universal and which depend on special arithmetic of \(\zeta\).

---

## 4. Proof discipline

### 4.1 Assumption ledger

Every theorem, lemma, notebook, and experiment must declare assumptions from this fixed vocabulary:

- `UNCONDITIONAL`
- `RH`
- `GRH(family)`
- `SIMPLE_ZEROS`
- `PAIR_CORRELATION_CONJECTURE`
- `N_LEVEL_CORRELATION_CONJECTURE`
- `ZERO_DENSITY(<exact statement>)`
- `SUPPORT(<region>)`
- `NUMERICAL_CERTIFICATE(<range>)`
- `SYNTHETIC_MODEL`

If a result uses none, mark it `UNCONDITIONAL` explicitly.

The word “unconditional” is prohibited if any hidden dependency uses an unproved hypothesis.

### 4.2 Theorem ledger

Maintain `research/theorem-ledger.yaml`. Each claim gets:

- stable ID;
- exact statement;
- status: `idea | heuristic | numerically-observed | proved-draft | independently-checked | formalized | submitted | published`;
- assumptions;
- dependencies by ID;
- source file and line/label;
- whether constants are effective;
- whether all limit interchanges are justified;
- whether computation is used in the proof;
- certificate/artifact hash if computation is used.

No abstract, introduction, talk, or README may state a result more strongly than the ledger entry.

### 4.3 Limit-order discipline

Higher-correlation work is highly vulnerable to illegitimate limit interchange. Every proof involving more than one parameter must specify the order of limits.

Typical parameters include
\[
T,\quad X,\quad N,\quad \varepsilon^{-1},\quad \text{support radius},\quad \text{smoothing width}.
\]

Whenever possible, prove a uniform bound that makes the order irrelevant. Otherwise state the order literally.

### 4.4 Sum/integral interchange checklist

Before interchanging a zero sum, prime sum, integral, expectation, or limit, cite one of:

- absolute convergence;
- dominated convergence with an explicit dominating function;
- Tonelli/Fubini with hypotheses verified;
- a truncated identity plus a separately proved tail bound;
- a distributional identity in a specified test-function space.

“Formally” is acceptable in scratch notes only, never in a proof draft.

### 4.5 Error terms

Never collapse several errors into \(O(\cdot)\) until their uniformity has been checked.

During derivation, name them:

- `E_height`
- `E_smoothing`
- `E_primepowers`
- `E_offdiag`
- `E_arch`
- `E_trunc`
- `E_supportboundary`
- etc.

Record parameter dependence. Only combine at the final optimization stage.

### 4.6 Fourier-support boundaries

If a theorem is proved for support in the **interior** of a polytope, do not report the closed polytope. Boundary extension requires an independent continuity/density argument with uniform constants.

### 4.7 Multiplicity

Do not infer simplicity from distinct ordinates without proof. Distinguish:

- zero counted with multiplicity;
- distinct complex zero;
- distinct ordinate.

Every proportion must state its denominator convention.

### 4.8 Symmetry

Use the functional-equation symmetry explicitly rather than implicitly. For horizontal observables, prefer even functions of \(\beta-1/2\) unless an asymmetric observable is deliberately paired with its reflected version.

---

## 5. Experimental mathematics policy

The experimental program has three valid purposes:

1. **verification** — catch algebraic/sign/normalization errors by testing known identities;
2. **discovery** — propose kernels, support regions, inequalities, or combinatorial decompositions;
3. **certification** — rigorously prove finite numerical inequalities used inside a theorem.

It does **not** empirically test whether unknown high zeros are off the critical line.

### 5.1 Critical warning about zero datasets

Certified zeta-zero datasets in computationally accessible/verified ranges consist of zeros proven to lie on the critical line. Therefore they contain essentially no empirical variation in \(\beta\) from which to infer the behavior of hypothetical off-line zeros.

Consequences:

- use real zero data to validate the **vertical** side of formulas;
- use analytic inequalities to obtain real horizontal conclusions;
- use synthetic off-line configurations only for sensitivity analysis and falsification of proposed inequalities;
- never cite synthetic experiments as evidence for or against RH.

### 5.2 Numerical rigor levels

Every numerical artifact must be tagged:

- **L0 exploratory:** ordinary floating point; not citable in a theorem.
- **L1 high precision:** arbitrary precision without rigorous enclosure; useful for discovery only.
- **L2 interval/ball certified:** every value enclosed rigorously; may support a theorem if the algorithmic reduction is proved.
- **L3 independently certified:** L2 result reproduced by an independent implementation/library or formal checker.

A publishable computer-assisted lemma should normally be L2 and, for a central claim, L3.

### 5.3 Required certification pattern

For a computer-assisted inequality:

1. derive mathematically a finite verification problem;
2. state the exact domain and all singular/boundary cases;
3. partition the domain deterministically;
4. evaluate with directed-rounding interval/ball arithmetic;
5. increase precision or subdivide whenever an interval straddles the decision boundary;
6. record all unresolved boxes; the run passes only if this set is empty;
7. emit a machine-readable certificate containing bounds, precision, subdivision tree or sufficient replay data, software versions, and source commit;
8. independently replay the certificate.

Never “round away” an inconclusive interval.

### 5.4 Rigorous quadrature

If an integral contributes to a proved constant:

- prefer analytic evaluation when possible;
- otherwise use rigorous interval quadrature with a proved derivative/tail bound;
- split at nonsmooth points and near singularities;
- prove the tails separately;
- store the enclosure, not just decimal digits.

### 5.5 Optimization

Floating-point LP/SDP/nonlinear optimizers are **candidate generators only**.

For a publishable optimum or feasible kernel:

- reconstruct coefficients as rationals/algebraic numbers when practical;
- otherwise enclose coefficients in certified intervals;
- prove all normalization, support, sign, and PSD constraints independently;
- for PSD matrices, use exact LDLᵀ where rational, or interval Cholesky/eigenvalue lower bounds;
- produce a rigorous objective-value interval;
- for claimed optimality, provide a certified dual witness or analytic extremality proof.

Do not cite an optimizer's “optimal” status flag as proof.

### 5.6 Randomized searches

Randomness may be used for discovery only unless the theorem itself is probabilistic.

Every randomized run must record:

- PRNG algorithm;
- seed;
- sample count;
- proposal distribution;
- acceptance/filter rules.

Any final deterministic theorem object must be independent of the random seed.

### 5.7 Synthetic off-line zero models

When testing horizontal sensitivity, generate synthetic configurations satisfying at minimum
\[
\rho,\quad 1-\rho,\quad \bar\rho,\quad 1-\bar\rho.
\]

Model classes should include:

- one isolated symmetric quartet;
- sparse quartets with density tending to zero;
- horizontal displacement \(c/\log T\);
- displacement \(c/(\log T)^\alpha\);
- clustered off-line zeros;
- repeated/multiple zeros;
- adversarial configurations chosen to preserve pair statistics while changing 3-level statistics.

These are **counterexample generators for methods**, not models of what zeta actually does.

### 5.8 Independent reproduction

Any numerical table or figure entering a paper must be generated from a script in `experiments/` and regenerated in CI at reduced scale. Full-scale runs must have content-addressed manifests in `artifacts/`.

At least one central numerical result must be independently reproduced using a second path, e.g.:

- Python + python-flint versus direct FLINT C;
- FLINT/Arb versus PARI/GP for overlapping computations;
- numerical PSD certificate versus Lean-checked exact matrix inequality.

---

## 6. Software stack

Favor a **small, auditable, open-source stack**. Add dependencies only when they buy a specific mathematical capability.

### 6.1 Primary language: Python

Use modern CPython (pin the exact supported minor version in the lockfile) for:

- experiment orchestration;
- symbolic bookkeeping;
- test-function construction;
- data processing;
- optimization front ends;
- plotting;
- certificate generation.

Package/environment management: **`uv`** with a committed lockfile.

Core packages:

- `python-flint` — rigorous `arb`/`acb` ball arithmetic and access to FLINT functionality;
- `sympy` — symbolic algebra and exact rational manipulation where appropriate;
- `numpy` / `scipy` — exploratory numerical linear algebra only, never the final certification layer;
- `mpmath` — exploratory high-precision cross-checks only;
- `pandas` or `polars` — experiment tables/manifests if needed;
- `matplotlib` — figures;
- `pytest` — unit/property/regression tests;
- `hypothesis` — property-based tests for algebraic identities and invariances;
- `cvxpy` — candidate generation for convex/semidefinite optimization where useful.

Do not use NumPy/SciPy double precision for a numerical lemma in a theorem.

### 6.2 Rigorous numerics: FLINT/Arb

**FLINT/Arb is the canonical numerical proof engine.**

Reasons:

- arbitrary-precision midpoint-radius ball arithmetic;
- rigorous real and complex enclosures;
- Riemann zeta, Hardy Z, zero-counting, and zeta-zero routines;
- mature special-function and polynomial infrastructure;
- direct C API for high-performance certification runs.

Use `python-flint` during development. Move bottleneck routines to direct FLINT C only after profiling and preserve identical input/output certificate formats.

Never assume an enclosure is tight merely because it is rigorous. If a ball is too wide to decide a sign/inequality, increase precision, reformulate, or subdivide.

### 6.3 Independent arithmetic cross-check: PARI/GP

Use PARI/GP, optionally through `cypari2`, as an independent implementation for overlapping scalar computations, special values, Dirichlet-series checks, and sanity tests.

PARI/GP output is a cross-check unless explicit rigorous error control for the invoked routine is established.

### 6.4 SageMath: optional integration environment

Use SageMath selectively when its number-theory/combinatorics infrastructure saves substantial development time. Do not make Sage the irreducible core of the project if the same proof artifact can be represented directly using FLINT and Python.

### 6.5 Formal verification: Lean 4 + mathlib

Use Lean 4/mathlib for finite or foundational components with high proof-leverage:

- linear-algebra/Hilbert-space inequalities;
- PSD/rank/trace arguments;
- exact finite-dimensional extremal certificates;
- Fourier-transform normalization lemmas when reusable;
- finite combinatorial identities for n-level partition expansions;
- eventually selected analytic lemmas if mathlib coverage permits.

Mathlib contains a complex Riemann zeta function, completed zeta, analytic properties, and functional-equation infrastructure, but do not assume the full analytic-number-theory toolkit needed here is already formalized.

Formalization strategy:

1. prove mathematics conventionally first;
2. formalize the structurally delicate finite pieces early;
3. formalize a complete headline theorem only if library prerequisites make it realistic.

Do not let formalization block exploratory mathematics, but use it aggressively for short arguments whose failure would invalidate a large computation.

### 6.6 Performance code: C with FLINT

For certification tasks dominated by ball arithmetic or zeta routines, use C against FLINT directly.

Requirements:

- no bespoke floating-point interval type;
- no `-ffast-math` or equivalent unsafe transformations in proof-critical code;
- deterministic output for fixed input/precision;
- compiler and FLINT version recorded;
- sanitizers enabled in test builds.

Avoid adding C++, Rust, Julia, or another performance language unless profiling shows a concrete need not met by Python + C/FLINT.

### 6.7 Writing and bibliography

Use:

- LaTeX;
- `latexmk`;
- BibLaTeX/Biber or a journal-compatible BibTeX workflow;
- semantic macros for every recurring mathematical object;
- `cleveref`/`hyperref` where journal style permits.

Every theorem label in the paper should map to an entry in the theorem ledger.

### 6.8 Reproducible environment

Use **Nix** as the top-level reproducibility layer if feasible for the team, with:

- `flake.nix` / `flake.lock`;
- pinned FLINT;
- pinned Python toolchain;
- pinned Lean toolchain;
- exact LaTeX environment where practical.

Also commit:

- `uv.lock`;
- `lean-toolchain`;
- `lake-manifest.json`;
- compiler version metadata for proof-critical C builds.

For collaborators who cannot use Nix, provide an OCI container definition with a pinned digest. The container is a convenience mirror; the lockfiles remain the source of dependency truth.

---

## 7. Repository layout

```text
.
├── AGENTS.md
├── README.md
├── CITATION.cff
├── LICENSE
├── pyproject.toml
├── uv.lock
├── flake.nix
├── flake.lock
├── lean-toolchain
├── lakefile.toml
├── lake-manifest.json
├── src/
│   ├── correlations/          # symbolic/numeric correlation machinery
│   ├── explicit_formula/      # explicit-formula transforms and components
│   ├── kernels/               # test functions and extremal-kernel definitions
│   ├── rigorous/              # ball-arithmetic certification code
│   ├── synthetic/             # synthetic off-line configurations
│   └── common/                # conventions, transforms, serialization
├── csrc/
│   └── flint_cert/            # performance-critical FLINT certification tools
├── lean/
│   └── HigherCorrelations/    # formalized finite/analytic components
├── research/
│   ├── theorem-ledger.yaml
│   ├── assumptions.md
│   ├── notation.md
│   ├── dependency-graph.md
│   ├── questions.md
│   └── dead-ends.md
├── proofs/
│   ├── pair_baseline.tex
│   ├── triple_explicit_formula.tex
│   ├── horizontal_extraction.tex
│   └── barriers.tex
├── experiments/
│   ├── manifests/
│   ├── pair/
│   ├── triple/
│   ├── kernels/
│   └── stress_tests/
├── tests/
├── data/
│   ├── raw/                   # immutable external data, checksummed
│   ├── derived/               # regenerable
│   └── schemas/
├── artifacts/
│   ├── certificates/
│   ├── tables/
│   └── figures/
├── paper/
│   ├── main.tex
│   └── references.bib
└── scripts/
    ├── reproduce.sh
    ├── verify_certificates.sh
    └── build_paper.sh
```

`data/raw/` is immutable. Generated files never overwrite raw inputs.

---

## 8. Test strategy

### 8.1 Unit tests

Test:

- Fourier-transform convention on Gaussians and compactly supported examples;
- functional-equation symmetry transformations;
- diagonal/partition enumeration for \(n=2,3,4,5\);
- invariance under permutation of tuple indices where mathematically expected;
- exact rational kernel identities;
- serialization/deserialization of certificates;
- precision monotonicity of rigorous bounds where applicable.

### 8.2 Golden tests

Reproduce known results in project normalization:

- a standard explicit-formula identity;
- a classical pair-correlation special case;
- known low zeta zeros and zero counts;
- selected integrals with exact values;
- a known PSD/rank-trace inequality instance.

Golden tests are regression guards, not evidence for a new theorem.

### 8.3 Property-based tests

Generate admissible test functions/configurations and check algebraic invariants:

- conjugation/reflection symmetry;
- scaling covariance;
- permutation invariance;
- cancellation of terms predicted by support;
- equality of two independently derived finite expansions.

### 8.4 Differential testing

For overlapping domains, compare:

- SymPy exact result vs FLINT enclosure;
- python-flint vs direct FLINT C;
- FLINT vs PARI/GP numerical values;
- symbolic partition generator vs brute-force enumeration at small \(n\).

Any discrepancy is treated as a bug until explained.

---

## 9. Experimental record format

Every experiment directory must contain `manifest.yaml` with:

```yaml
id: EXP-YYYY-NNN
purpose: discovery | verification | certification
claim_ids: []
commit: <git sha>
environment:
  nix_lock_hash: <hash>
  uv_lock_hash: <hash>
  flint_version: <version>
  python_version: <version>
inputs:
  description: ...
  sha256: ...
precision:
  bits: ...
randomness:
  algorithm: null
  seed: null
outputs:
  files: []
  sha256: []
result:
  status: pass | fail | inconclusive
  rigorous: false
notes: ...
```

For interval certification, `rigorous: true` is permitted only if every operation relevant to the conclusion has a proved enclosure path.

---

## 10. Literature and provenance workflow

### 10.1 Source hierarchy

Prefer:

1. published journal article;
2. author's current arXiv version;
3. author's notes/talk for intuition only;
4. secondary exposition;
5. informal discussion only as a pointer.

When a result is new and only on arXiv, label it `PREPRINT` in notes and manuscript drafts.

### 10.2 Seed literature

Begin with, and then citation-chain outward from:

- H. L. Montgomery, *The pair correlation of zeros of the zeta function* (1973).
- Z. Rudnick and P. Sarnak, *Zeros of principal L-functions and random matrix theory*, Duke Math. J. 81 (1996), for n-level correlations and restricted Fourier support.
- S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya, C. L. Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair correlation of zeros of the Riemann zeta function*, arXiv:2306.04799.
- S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya, C. L. Turnage-Butterbaugh, *Pair Correlation of Zeros of the Riemann Zeta Function I: Proportions of Simple Zeros and Critical Zeros*, arXiv:2501.14545.
- D. A. Goldston and A. I. Suriajaya, *Zeta Zeros on the Critical Line*, arXiv:2511.20059.
- L. Alpöge and R. Furman, 2026 preprint on more than two thirds of zeta zeros being simple and on the critical line; verify the current arXiv metadata before citing.
- Y. Lamzouri, *A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line*, arXiv:2609.02882.
- J. B. Conrey and N. C. Snaith, *In support of n-correlation*, arXiv:1212.5537, for support/combinatorial perspective and comparison with random-matrix formulas.
- Weil explicit-formula literature and modern expositions of Weil's criterion.

Maintain `research/literature.bib` and `research/literature-notes/`. Each note must list exactly which lemma, convention, or idea is being imported.

### 10.3 No citation laundering

If an exposition says “it is known that X,” locate the original or a reliable primary source before using X in a proof.

---

## 11. First concrete theorem targets

These are **targets, not claims**.

### Target T1 — Unconditional smoothed 3-level formula in a small support region

Prove a 3-level correlation asymptotic for a symmetric Schwartz test function \(F:\mathbb R^2\to\mathbb C\), with \(\widehat F\) compactly supported in an explicitly stated neighborhood of the origin, without assuming RH.

Success criterion: a main term matching the expected critical-line/random-matrix expression in the admissible region plus an unconditional error \(o(\text{main scale})\), while the proof retains all off-line zero contributions correctly.

### Target T2 — Horizontal-sensitive 3-level inequality

Construct a nonnegative or PSD functional built from T1 whose zero-side expansion contains a strictly increasing penalty for nonzero
\[
|\beta-1/2|.
\]

Success criterion: an unconditional inequality not obtainable from pair correlation alone.

### Target T3 — Quantitative consequence

Deduce at least one of:

- a better lower bound for the proportion of zeros on the line;
- a better lower bound for simple critical-line zeros;
- an upper bound on a nontrivial horizontal moment;
- a theorem excluding a class of sparse symmetric off-line configurations.

The improvement need not initially beat the best published numerical percentage if it is structurally new and demonstrably uses 3-level information. A method that is provably stronger after future support enlargement is worthwhile.

### Target T4 — Pair-information barrier

Formulate the best possible horizontal conclusion from the currently available unconditional pair-correlation information plus the chosen positivity class. Solve or tightly bound the corresponding extremal problem.

This provides the baseline showing what 3-level information must improve.

### Target T5 — Higher-level abstraction

Give a general partition/cumulant formula that recovers \(n=2,3\) and isolates the arithmetic input needed for general \(n\).

---

## 12. Suggested initial experiments

These experiments are chosen because a negative result is informative.

### Experiment E1 — Pair-method reconstruction

Numerically reconstruct the current pair-correlation horizontal-information inequality with project conventions. Verify constants with Arb. Then derive a dual certificate for the best bound obtainable within the exact chosen kernel family.

Purpose: validate the toolchain and discover whether optimization slack remains.

### Experiment E2 — Triple-kernel basis search

Parameterize \(\widehat F\) using compactly supported tensor-product B-splines, symmetric polynomials times bump functions, or finite autocorrelation bases. Impose symmetry under the \(S_3\) action induced by permuting zeros.

Optimize candidate horizontal penalties subject to conjectured/proved positivity constraints. Use floating-point SDP for discovery only; certify selected candidates afterward.

### Experiment E3 — Adversarial zero configurations

Construct synthetic zero sets that match a prescribed pair statistic to high accuracy but have different 3-level statistics and different fractions of off-line zeros.

Purpose: demonstrate what extra information 3-level data can theoretically distinguish and identify observables with maximal horizontal sensitivity.

### Experiment E4 — Support-polytope enumeration

Encode the prime-side frequency constraints combinatorially. Automatically enumerate which index/sign patterns survive a proposed Fourier-support region for \(n=3,4\).

Use exact rational polyhedral computation if possible. Every automatically generated case split must be independently brute-force checked for small instances.

### Experiment E5 — Moment/PSD hierarchy

Construct truncated moment matrices for the scaled horizontal displacement variable under the symmetry \(x\mapsto-x\). Determine which moments could in principle be bounded by pair versus triple data. Search for dual polynomials proving tail bounds.

Purpose: translate “more correlation information” into an explicit moment-problem language.

---

## 13. Agent operating rules

### 13.1 Before changing mathematics

An agent must:

1. read `research/notation.md`;
2. read relevant theorem-ledger entries;
3. search for an existing lemma before introducing a duplicate;
4. state whether the task is proof, heuristic, experiment, or exposition;
5. identify assumptions before manipulating formulas.

### 13.2 When deriving formulas

- Keep \(\beta\) symbolic.
- Do not replace sums over zeros by sums over ordinates unless multiplicity and horizontal dependence are accounted for.
- Keep smoothing until error terms are under control.
- Expand 3-level diagonals systematically using partitions.
- Check every result under \(\rho\mapsto1-\bar\rho\).
- Perform a dimensional/scale check after every Fourier transform.
- Test special cases that collapse to the 2-level formula.

### 13.3 When using a CAS or LLM

CAS/LLM output is conjectural scratchwork until independently checked.

For symbolic identities:

- simplify both sides to a canonical exact form when feasible;
- differentiate/integrate back as a check;
- verify on exact rational/algebraic test points;
- if an identity enters a proof and is nontrivial, prove it mathematically or formalize it.

Never cite an LLM as a source for a mathematical fact.

### 13.4 When a proof attempt fails

Record useful failures in `research/dead-ends.md` with:

- attempted statement;
- exact obstruction;
- whether obstruction is technical or structural;
- smallest counterexample if any;
- what extra input would repair it.

Do not repeatedly rediscover the same dead end.

### 13.5 Claim language

Use:

- “proves” only for a complete proof;
- “certifies” for a rigorous finite computation;
- “suggests” for numerical evidence;
- “is consistent with” for finite-height agreement;
- “would imply” for conditional chains.

Never write “shows RH is likely true” based on project computations.

---

## 14. Publication bar

Before a result is submitted, require all of the following.

### Mathematics

- Every theorem has an assumption ledger entry.
- Pair/3-level normalization has been independently checked.
- All diagonal terms and multiplicities have been audited.
- Every limit/sum/integral interchange is justified.
- Fourier-support conditions are explicit.
- Error terms are uniform in every parameter used later.
- Claims of unconditionality have passed the RH-contamination audit.

### Computation

- Proof-critical numerics use rigorous enclosures.
- Full manifest and hashes exist.
- Certificates replay from a clean environment.
- Central computations have an independent cross-check.
- Figures can be regenerated from source data.
- No decimal constant is quoted more accurately than its rigorous enclosure permits.

### Reproducibility

A clean machine must be able to run, at minimum:

```bash
nix develop
uv sync --frozen
pytest
lake build
./scripts/verify_certificates.sh
./scripts/build_paper.sh
```

If full computations are too expensive for CI, CI verifies reduced instances plus stored full-scale certificates.

### Exposition

The paper must explicitly separate:

- proved theorem;
- heuristic/random-matrix prediction;
- numerical experiment;
- conditional consequence;
- open problem.

The introduction must state why the result gives information unavailable from pair correlation alone, if that is claimed.

---

## 15. Decision rules for research direction

At each quarterly research checkpoint, rank active directions using:

\[
\text{priority}
=
\frac{
\text{expected theorem value}\times
\text{structural novelty}\times
\text{reusability}
}{
\text{unresolved hard inputs}\times
\text{proof fragility}
}.
\]

This is a planning heuristic, not a scientific score.

Prefer a modest theorem with a clean unconditional mechanism over a spectacular statement resting on an unproved prime-correlation estimate.

Stop or park a line of attack when:

- its 3-level theorem requires an arithmetic input essentially equivalent to the desired conclusion;
- the support restriction annihilates every genuinely 3-level term, reducing the result to pair information;
- the horizontal extraction inequality is provably dominated by the existing pair-correlation bound;
- numerical optimization repeatedly converges to a certified dual barrier showing no improvement in the chosen function class.

A barrier is a result, not a failure.

---

## 16. Near-term roadmap

### Phase 0 — Reproducibility and notation

- freeze Fourier/scaling conventions;
- establish the environment;
- populate theorem and literature ledgers;
- reproduce certified zeta-zero and zero-count examples;
- formalize basic finite linear-algebra inequalities used by the pair method.

### Phase 1 — Pair baseline and barrier

- reconstruct the unconditional pair-correlation argument;
- implement kernel optimization;
- certify the pair-information optimum within a clearly defined admissible class;
- identify precisely what statistic a third level would need to control to improve it.

### Phase 2 — 3-level formula

- derive with heavy smoothing;
- classify partitions/diagonals;
- prove the first nonempty support region;
- compare the resulting main term against random-matrix expectations only after the unconditional derivation is complete.

### Phase 3 — Horizontal extraction

- build PSD/Hilbert-space functionals using the new 3-level information;
- solve primal/dual extremal problems;
- certify candidate kernels;
- seek first unconditional horizontal consequence genuinely stronger than pair-only information in some metric.

### Phase 4 — Generalization

- abstract the partition/cumulant machinery;
- attempt 4-level in the smallest tractable support region;
- test portability to Dirichlet \(L\)-function families.

---

## 17. Definition of project success

The project is successful if it produces a rigorous answer to either of these questions:

> **What unconditional 3-level or higher correlation information can currently be proved for zeta zeros without assuming RH?**

and

> **Exactly what new constraints on \(\Re\rho\) follow from that information that do not follow from pair correlation alone?**

A result showing that the available higher-correlation information still cannot improve horizontal control is also valuable if it is sharp enough to identify the missing ingredient.

The project should optimize for **correct structural knowledge**, not for a headline percentage.

---

## 18. Software/reference notes

The numerical-stack choice is grounded in current capabilities:

- FLINT's `acb_dirichlet` module contains rigorous routines for Riemann zeta, Hardy Z, zero counting, and zeta zeros: <https://flintlib.org/doc/acb_dirichlet.html>
- Arb/FLINT uses arbitrary-precision ball arithmetic with enclosure semantics: <https://www.arblib.org/> and <https://arblib.org/using.html>
- `python-flint` exposes Arb/Acb to Python, including zeta evaluation and zeta-zero routines: <https://python-flint.readthedocs.io/>
- mathlib contains a complex Riemann zeta function and completed-zeta analytic infrastructure: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html>

These capabilities may change. Pin versions, and verify the semantics of every routine used in a proof-critical path against the versioned documentation and source.
