# Weighted main-term comparison in Lean

Assumptions: `UNCONDITIONAL`; the weighted bounds and limits additionally use
`SUPPORT(h<=1-kappa, kappa>0)` and the existing `TripleBudgetWeight` smoothing
hypotheses. The usual nontrivial range is `0<kappa<1`. The Lean bounds also
allow larger margins, which force a smooth test to vanish.

This milestone checks the exact sine-benchmark comparison and the two weighted
asymptotic consequences of `TRIPLE-MAIN-TERM-COMPARISON-001`. Its historical
claim remains `proved-draft`. Analytic coverage is **partial**: the inherited
uniform constants are proved to exist, independently of height, margin, test
and smoothing; their numerical effectiveness is not certified here.

## Exact conventions and interfaces

`mainTermFrequencyTest` lifts an arbitrary smooth compactly supported complex
function phi from ordinary real pairs to the existing measure-preserving
`FourierPlane`. `mainTermPhysicalTest` is its positive-inverse Schwartz Fourier
transform. Its values on the real plane equal the existing `complexFourier`
function, and its forward transform recovers phi exactly.

The benchmark uses all five occurrence-index partitions, with line measures
parameterized by coordinate dr. It is invariant under simultaneous reflection.
Thus its pairing with the positive-inverse transform equals the checked
frequency-side spectrum paired with phi. There is no reality, evenness or
conjugation assumption on phi.

For any Schwartz frequency test supported in the closed hexagon h<=1,
the planar cumulant-density product is zero. On all three frequency lines,
1-tau(r) may be replaced by |r| wherever the test is nonzero. Integrability
of the three resulting traces is inherited from the checked spectral pairing
before the integrals are combined. For smooth compact phi this proves

    S3[F] = phi(0,0) + integral |r| (phi(r,0)+phi(0,r)+phi(r,-r)) dr,
    signedLimit(phi) = (3/2) S3[F].

The line-gauge identity covers both signs of r, including the origin and
boundary vertices; the closed-support theorem includes every internal seam.
Explicit zero-test identities check the degenerate case. The deterministic
closed support statement does not extend any zeta theorem to h=1.

## Weighted bounds and limits

Write B=T/(2 pi), b=log B and L=log(2T+2). The new comparison wrappers preserve
the witnesses supplied by `signed_uniform_bound` and
`frozenStatistic_uniform_bound`. For T>=2 pi exp(1) and support h<=1-kappa,

    |signedStatistic - (3/2) S3[F]|
      <= A signedC1(phi) (1+M0+fourierDerivativeL1(omega,1))
           (1/b + B^(-kappa) L^3),
    |frozenStatistic - (3/2) S3[F]|
      <= the same signed error + C tripleTestL1(phi) (M0+M1) B^(-kappa) L^3.

Here M0 bounds |omega| and M1 is a nonnegative Lipschitz bound. A separate
wrapper accepts a bound on |omega'| and derives the Lipschitz hypothesis.
The derivative supremum bound is distinct from the derivative L1 norm in
the signed error. No new error term or enlargement of either constant is
introduced by the comparison.

For fixed smoothing, test and positive margin, both statistics converge to
(3/2) S3[F], and multiplying each statistic by 2/3 gives limit S3[F]. Compact
support in the open hexagon supplies a fixed positive margin, giving corresponding
compact-interior corollaries. No varying-margin limit is asserted.

The earlier local critical normalization is still exactly 3b/(2 log T), with
limit 3/2; the comparison does not substitute the limiting factor at finite
height. Native and frozen statistics retain the previously checked full
complex zero arguments and horizontal kernels. No zero sum is redefined and
no additional infinite-sum interchange is required.

## Verification and scope

Run

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-main-term-comparison-only
```

The dedicated suite checks **29 statements in five modules**, with eight
unfinished-proof rejection controls: the Fourier adapter, reflection, closed
support cancellation, exact comparison, signed bound, derivative-form frozen
bound, and both normalized limits. Contracts import only the new definitions
module. The allowed axioms remain `propext`, `Quot.sound`, and `Classical.choice`;
nanoda is disabled. The focused runner also performs the combined build,
complete axiom audit, coverage, harness, control-pool and pair/triple regressions.
It reuses the existing four-worker rejection-control pool.

The ledger adds a separate formal claim after successful verification, and
pair/triple audit ledger hashes are refreshed without changing their historical
review scope or dependency graph. The prior ledger is preserved as a byte prefix.
The assembled unit-normalized smoothed theorem is the next composition step.
Effectivity of inherited constants, an ordinate-only statistic, and weighted
zeta cumulant subtraction remain separate obligations.
