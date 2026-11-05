# Kernel localization: Lean verification

## Exact decomposition (previous stage)

Task: formal verification. Assumptions: `UNCONDITIONAL`.
The exact-decomposition milestone is complete. The focused suite passed all
14 statement comparisons across three modules, both unfinished-proof rejection
controls, the combined build, complete axiom report, coverage, harness and
pair/triple regressions. The formal ledger entry is
`MASTER-KERNEL-LOCALIZATION-IDENTITY-FORMAL-001`.

Certificate: [PASS manifest](../artifacts/certificates/lean/cb642dcc43967da2bd3328a5f8e0f32697b0b5f4abf892136165be98eb35aba7/manifest.json).
The certificate records the source and challenge hashes for that stage.
The quantitative extension below supersedes its inventory and assembly module;
the original identity proof and historical RH-audit scope are unchanged.

This first stage proves, for continuous real omega supported in [1,2], T>0,
and every ordered actual occurrence triple (j,k,l),

K_T(j,k,l) = omega(gamma_l/T) J(gamma_j-gamma_l,gamma_k-gamma_l;delta)/T
             + E_kernel(j,k,l).

E_kernel is defined by the explicit integral of
[omega((gamma_l+v)/T)-omega(gamma_l/T)] times the three-factor profile,
with the outside factor 1/T. It is not defined as the kernel difference.
The two weighted profile terms are proved integrable before subtracting their
integrals; the scaled error integrand is absolutely integrable.

The translation t=gamma_l+v retains the third factor's negative displacement,
which corresponds to the conjugated anchor's positive imaginary center.
The existing rational-profile evaluation supplies J. The test-order interface
uses the existing permutation (i1,i2,i3) -> (i2,i3,i1) and actualRationalKernel.
No extra factor eight enters K_T. Both ordinate signs, multiplicities, repeated
occurrences, equal ordinates and coincident centers are included. The zero
weight and fully repeated tuple are checked explicitly, retaining displacement.

This milestone concerns fixed tuples at fixed height. It does not establish
the quantitative tuplewise bound, the near/far decomposition, summed errors,
explicit-profile correlation transfer or a height limit. The historical
TRIPLE-KERNEL-LOCALIZATION-001 entry retains partial formalization coverage.
No RH, simplicity or critical-line substitution is used.

The focused suite covers every public declaration with definition-only expected
statements and two rejected unfinished-proof controls (translation and exact
decomposition), plus the combined project build, full axiom report, analytic
coverage, harness and pair/triple regressions. Only propext, Quot.sound and
Classical.choice are permitted.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only
```

## Quantitative fixed-tuple extension (complete)

Formal ledger entry: `MASTER-KERNEL-LOCALIZATION-BOUND-FORMAL-001`.
The full focused suite passed all 28 statement comparisons, four rejection
controls, the combined build, axiom audit and regressions.
Certificate: [PASS manifest](../artifacts/certificates/lean/b297cd3415f733367b4b5edf5ead3d7f7066bd8e89dd90b82ee8bdecf54ed966/manifest.json).
This certificate records the sources for the tuplewise stage. The summed
extension below supersedes its assembly and inventory; the tuplewise proof
module is unchanged.

The next stage proves the manuscript's exact bound

||E_kernel(v)|| <= 64 pi M / (27 T^2 (4+(gamma(v0)-gamma(v1))^2)).

Here T>0, M>=0 is an explicit global Lipschitz constant for the real weight,
with no support hypothesis required for the error integral. A derivative
wrapper takes a differentiable weight and |deriv omega(x)|<=M for every real x.
For the manuscript's compact smooth weight, M may be Wprime_inf. This is a
uniform bound for each given derivative bound, with no existential loss in its
64pi/27 coefficient. Compact support in [1,2] is required only by the existing
exact-decomposition interface used in the kernel-difference corollaries.

The proof strengthens the scalar kernel estimate on the closed half-strip
|delta|<=1/2 to (4/3)/(1+x^2), preserving the older enlarged-strip bounds.
It specializes the checked pair-kernel integral to the real two-center
majorant, including coincident centers. Multiplying the three scalar bounds
and using |u|/(1+u^2)<=1/2 gives the integrable majorant

(32 M/(27 T)) / ((1+(u-a)^2)(1+(u-b)^2)).

Its integral is (32 M/(27 T))*2pi/(4+(a-b)^2). The outside 1/T
in the error definition supplies T^(-2). The new proof also establishes
integrability directly for Lipschitz weights, including weights without
compact support. No infinite sum or limit is exchanged.

Master order uses the non-anchor gap gamma(v0)-gamma(v1). Under the existing
test permutation this becomes gamma(v1)-gamma(v2), while the frozen weight
remains anchored at gamma(v0). Equal non-anchor ordinates give the finite bound
16 pi M/(27 T^2); repeated occurrences and distinct zeros at the same ordinate
are both allowed. The closed scalar-strip theorem covers both horizontal
endpoints without a critical-line substitution. Zero smoothing remains covered
by the earlier exact zero-error theorem.

The extended suite contains 28 public statements in four modules. Four
unfinished-proof controls cover translation, decomposition, the sharper scalar
bound and the final tuplewise estimate. The separate summed near/far estimates,
correlation transfer, and height limit remain pending. The tuplewise bound is
not used as a summable bound over all triples. The ordinate-only signed error
remains open.

## Summed near/far extension (complete)

Formal ledger entry: `MASTER-KERNEL-LOCALIZATION-SUM-FORMAL-001`.
All 71 statement comparisons, nine rejection controls, the combined build,
axiom audit and regressions passed.
Certificate: [PASS manifest](../artifacts/certificates/lean/6a35fdbed75bfc10efbec04f4a43f6e5c4078c22472bafaa86daf718386889db/manifest.json).
This certificate records the regional summed-error stage. The frozen-profile
extension below supersedes its assembly and inventory; the regional proof
modules are unchanged.

For T>=3 put L=log(2T+2). Let omega be real, supported in [1,2],
with |omega|<=M0 and global Lipschitz constant M1. The three regional errors
are integrals of the actual translated complex error density, including its
outside factor 1/T. Their regions are exactly:

- near: |t-gamma_l|<=T;
- far-center: |t-gamma_l|>T and t in [T,2T];
- far-anchor: |t-gamma_l|>T, t outside [T,2T], gamma_l in [T,2T].

The distance boundary belongs to near. Both center-interval endpoints belong
to far-center when the distance is greater than T. The regions are disjoint;
outside their union the weight difference is zero. Integrability is established
before reconstructing E_kernel as the sum of these three complex integrals.

The stronger regional integral-norm budgets are summable over all MasterTriple
occurrences, with separate absolute constants independent of weight and height:

| Region | Sum of integral norms (and hence sum of error norms) |
|---|---|
| near | <= C_near M1 L^4/T |
| far-center | <= C_center M0 L^3/T |
| far-anchor | <= C_anchor M0 L^3/T |

Consequently sum_v ||E_kernel(v)|| <= C (M1 L^4+M0 L^3)/T.
A differentiable-weight wrapper takes an explicit bound |deriv omega|<=M1;
this is the derivative supremum dependence Wprime_inf, not the earlier
L1 derivative norm. The error retains every horizontal displacement, both
ordinate signs, repeated occurrences and distinct complex zeros sharing an
ordinate. No simplicity or critical-line substitution is used.

The near first moment uses unit shells and the checked harmonic-sum bound.
The strict far-center tail is dominated by the existing closed-tail estimate.
For far anchors, a scaled integrable profile

F(u) = (1+log(3|u|+2)^2)/(1+u^2)

provides the required logarithm-squared integral tail. Its integrability follows
from a (1+u^2)^(-3/4) majorant. This implements the manuscript tail estimate by
scaling rather than a new dyadic integral decomposition, with the same L^2/T
rate. Only the anchors are restricted to [T,2T]; the center integral includes
the entire real line, including both distant tails.

Finite rectangular occurrence sums are bounded first, followed by finite
sum/integral interchange and uniform finite integral-norm bounds. Those bounds
prove summability before infinite complex sum/integral interchange is invoked.
This finite-cutoff route replaces the planned nonnegative Tonelli construction
without introducing an unproved convergence hypothesis. The tuplewise bound
from the previous stage is not summed over all triples.

Constants are absolute and uniform but existential in Lean. The inherited
low-height counting constant and the profile integral are not numerically
certified here. The previous explicit tuplewise constant 64pi/27 is unchanged.
This stage left frozen-profile summability, complex-test correlation transfer
and the inherited height limit pending. The next section records the
unweighted frozen-profile summability milestone. The ordinate-only signed complex-argument error is still open.

The expanded suite covers all 71 public statements in 13 modules, with nine
unfinished-proof rejection controls: the preceding four plus region assembly,
near, far-center, far-anchor and combined summability. It also runs the combined
project build, full axiom report, coverage, harness and pair/triple regressions.

## Unweighted frozen-profile summability (complete)

Formal ledger entry: `MASTER-FROZEN-PROFILE-SUMMABILITY-FORMAL-001`.
All 88 statement comparisons, twelve rejection controls, the combined build,
axiom audit and regressions passed.
Certificate: [PASS manifest](../artifacts/certificates/lean/ab42ee3727e01132cf0817954f4012f687c26093aba1092fc8b7a5ccf8747587/manifest.json).
All Lean source and challenge hashes match this run; subsequent ledger and
audit metadata updates do not change the proof sources.

The frozen coefficient is defined directly, with the exact outside factor 1/T:

P_T(v) = omega(gamma(v2)/T) J(gamma(v0)-gamma(v2),gamma(v1)-gamma(v2);delta)/T.

It is not defined by subtracting two kernels. The checked identity subsequently
identifies P_T with K_T-E_kernel. For T>=3, support omega in [1,2], |omega|<=M0,
and global Lipschitz constant M1, its full occurrence series is absolutely
summable. With L=log(2T+2), there are absolute A,B>0, uniform in all displayed
parameters, such that

sum_v ||P_T(v)|| <= A M0 L^3 + B (M1 L^4 + M0 L^3)/T.

The proof also retains the unsimplified mass bound
sum ||P_T|| <= sum ||K_T|| + sum ||E_kernel||. The kernel bound uses the
unit-scale master identity and integral |omega|<=M0 from support of length one;
it does not require nonnegative smoothing or unit mass. The factor eight in
the master explicit formula is divided out when bounding K_T and never enters
the definition of P_T. The error uses the separately checked regional budgets.
A derivative wrapper accepts differentiability and |deriv omega|<=M1.

The test-order coefficient is omega(gamma(v0)/T) actualRationalKernel(v)/T.
The existing permutation identifies it exactly with P_T(tripleTestToMaster v)
and transfers the same absolute mass bound. Only after absolute summability is
proved are the complex sums added to obtain sum K_T = sum P_T + sum E_kernel,
in both tuple orderings.

Independent finite occurrence cutoffs converge to the full frozen sum in both
orderings. In master order this is also specialized to three independent closed
ordinate cutoffs |gamma|<=U_r. T is fixed while these cutoffs are removed;
no T-to-infinity assertion is made. Zero smoothing and a fully repeated
occurrence are checked explicitly. The repeated profile remains
J(0,0;delta,delta,delta), preserving its horizontal dependence and multiplicity.
Both ordinate signs and distinct complex zeros with equal ordinates remain.

This is summability of the unweighted coefficient series. It does not assert
summability after inserting an unbounded complex Fourier test. Complex-test
profile summability, its correlation transfer, and the inherited T-to-infinity
limit are the next steps. The ordinate-only signed error remains open.
Constants remain absolute existential constants, without numerical evaluation.

The expanded localization suite checks 88 public statements in 16 modules.
Its twelve unfinished-proof controls include frozen summability, normalization
and independent cutoff convergence, in addition to the preceding nine. The
focused harness also runs the combined build, full axiom audit, coverage,
harness and pair/triple regressions.
