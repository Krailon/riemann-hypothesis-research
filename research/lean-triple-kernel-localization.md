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
All Lean source and challenge hashes match this certified run. Subsequent
metadata updates record the result without changing proof sources.

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
