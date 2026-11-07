# Unit-normalized smoothed triple theorem

Assumptions: `UNCONDITIONAL`, `SUPPORT(h<=1-kappa, 0<kappa<1)` for the
standalone theorem, with existing `TripleBudgetWeight` smoothing hypotheses.
The main declaration is `HigherCorrelations.smoothedTriple_theorem`.

The observable `smoothedTripleStatistic` is exactly (2/3) times the existing
frozen statistic. Its checked profile-sum identity is

    R(T) = 16/(3 T log T) sum_v omega(gamma(v0)/T) J(v) F(z21,z31).

Here `smoothedTripleTerm` uses the actual rational profile and the existing
complex inverse Fourier transform. The profile identity exposes gaps
(gamma(v1)-gamma(v0), gamma(v2)-gamma(v0)) and horizontal parameters
(delta(v1),delta(v2),delta(v0)). The anchor has the positive imaginary center;
the test shifts contain sums of horizontal displacements. All ordered
occurrence triples are included, with multiplicities and both ordinate signs.
Only the anchor is height localized. Coincident indices require no exclusion.

Absolute convergence of the raw profile series follows by multiplying the
already summable frozen-profile norm series by |T|, with T>2pi. Independent
finite occurrence cutoffs and inclusive ordinate cutoffs converge at fixed T.
The normalized cutoff statements retain the coefficient 16/(3 T log T).
The five-partition sine benchmark is the checked `sineBenchmark` applied to
`mainTermPhysicalTest`; this is the positive-inverse Schwartz transform of the
compact smooth complex frequency test. All benchmark pairings are bilinear.

## Uniform error and limits

The two named bounds use B=T/(2pi), b=log B, L=log(2T+2):

    E_signed = signedC1(phi) (1+M0+||omega'||_1) (1/b+B^(-kappa)L^3),
    E_kernel = ||phi||_1 (M0+M1) B^(-kappa)L^3.

M0 bounds |omega| and M1 bounds |omega'|. The separate bound is
|R-S3| <= A E_signed+C E_kernel, for positive absolute existential constants.
The exact norm scaling by 2/3 produces these constants from the checked
comparison witnesses. Nonnegativity of both envelopes permits replacing the
two constants by their maximum to obtain C(E_signed+E_kernel).

`smoothedWeightSup` is the supremum of the range of |omega|. Smooth compact
support proves finiteness and pointwise control for omega and its derivative.
The standalone theorem uses these exact supremum norms and simultaneously
asserts absolute convergence and the uniform additive bound for T>=2pi exp(1).
The result applies when the benchmark is zero and to asymmetric complex tests.

The fixed-test limit and compact-interior support corollary follow from the
checked normalized comparison. The varying-family theorem is formulated over
an arbitrary index type and filter: tests, smoothing, bounds, heights and
positive margins may vary. Heights must eventually be at least 2pi exp(1),
and both named error envelopes must tend to zero. Then the norm of the
difference from the varying benchmark tends to zero. No fixed limiting
benchmark is assumed, and no interchange of a height limit with zero cutoffs
is used. This covers real-height families and sequences alike. The envelope
condition suffices without separately assuming the heights tend to infinity.

## Verification boundary

The dedicated inventory contains 20 public statements in four modules.
Nine unfinished-proof rejection controls cover normalization, summability,
both cutoff interfaces, profile conventions, the assembled uniform theorem,
supremum specialization, the fixed limit and the varying-family limit.
Expected contracts import only `SmoothedTripleDefinitions`. Permitted axioms
are `propext`, `Quot.sound`, and `Classical.choice`; nanoda is disabled.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-smoothed-correlation-only
```

The focused run includes the combined project build, complete axiom audit,
coverage, harness, control-pool and pair/triple regressions. Rejection controls
use the existing parallel pool. A separate formal ledger entry records the
successful certificate, preserving historical ledger entries as a byte prefix.

Coverage of `TRIPLE-SMOOTHED-CORRELATION-001` remains partial solely for the
uncertified numerical effectiveness of inherited uniform constants. The
historical statement and audit scope remain unchanged. The full horizontal
kernel and complex test arguments remain present. No outer support-boundary
extension, ordinate-only replacement or weighted zeta cumulant assertion is
part of this milestone.
