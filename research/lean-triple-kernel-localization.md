# Exact kernel-localization identity: Lean verification

Task: formal verification. Assumptions: `UNCONDITIONAL`.
The exact-decomposition milestone is complete. The focused suite passed all
14 statement comparisons across three modules, both unfinished-proof rejection
controls, the combined build, complete axiom report, coverage, harness and
pair/triple regressions. The formal ledger entry is
`MASTER-KERNEL-LOCALIZATION-IDENTITY-FORMAL-001`.

Certificate: [PASS manifest](../artifacts/certificates/lean/cb642dcc43967da2bd3328a5f8e0f32697b0b5f4abf892136165be98eb35aba7/manifest.json).
All Lean source and challenge hashes match the certified run. Subsequent ledger,
coverage and documentation updates record this result without changing proof
sources or extending the historical RH-audit scope.

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
