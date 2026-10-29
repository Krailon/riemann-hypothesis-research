# Frequency axes and origin: Lean verification

Task: formal verification. Assumptions: `UNCONDITIONAL` and
`SUPPORT(relative support in xi>=0, eta>=0, xi+eta<=1-kappa; kappa>0)`.

The milestone is complete. The focused reproduction passed, including all 143
statement comparisons, six rejected unfinished-proof controls, the combined
project build, complete axiom report, and analytic-coverage, harness and
pair/triple regressions. The separate formal ledger entry is
`MASTER-BOUNDARY-FORMAL-001`; historical effective-constant claims retain their
existing statuses.

Certificate: [PASS manifest](../artifacts/certificates/lean/6db5d078c7212b8bdfe6f7b6251b3aa6573149617e3147f3ae09af733dcfb419/manifest.json).
All Lean source and challenge hashes match the certified run. Subsequent
ledger, coverage and documentation updates record the result without changing
any proof source or extending the historical source-audit scope.

## Mathematical scope

For B=T/(2pi), b=log B, q=log T and L=log(2T+2), the development proves:

- The exact full-zero identity with factor 8/q, all ordered actual zero
  occurrences, multiplicities, both ordinate signs and all partial diagonals.
  The anchor permutation is (i2,i3,i1); the kernel already contains 1/T.
  The absolute frequency majorant before division by q is
  A ||psi||_(L1(Q)) B^(1-kappa) L^3. Independent occurrence cutoffs converge
  at fixed height before the height limit is taken.
- The entire extension of the quadrant transform, with Fourier inversion
  as a tempered distribution. Its zero extension is measurable and integrable;
  it is not assumed smooth or Schwartz across the axes.
- The exact origin mass 1/4 and each axis mass 3/4, using ordinary Lebesgue
  restriction to the closed quadrant, with no extra half weights.
- The uniform integrated bound
  integral_Q |psi R_T| <= C M (1+W_inf+W_1)(1+B^(-kappa)L^4),
  for T>=2pi exp(1), M>=sup_Q|psi|. C is selected before smoothing, height,
  support margin and test. The eight non-H errors, nineteen H words and
  retained evaluation errors are counted exactly once; the earlier 208
  component refinement remains available.
- The manuscript seminorm N1(psi), defined as the sum of the suprema on Q
  of |psi| and its two coordinate derivatives. It controls the real Frechet
  derivative in the product norm. Exact dilation and the transverse axis
  substitution give quantitative trace approximations with integrability
  verified before splitting any integral.
- The normalized asymptotic

  |B_T[psi] - psi(0,0)/4 - (3/4) integral_0^infinity
      r(psi(r,0)+psi(0,r)) dr|
    <= C N1(psi)(1+W_inf+W_1)(1/b+B^(-kappa)L^3).

  It yields the fixed-test height limit. The proof explicitly converts
  b=log(T/(2pi)) to q=log T. The upper support margin stays positive;
  axes and origin are included.
- For fixed smoothing, q^(-3) C_3,T(exp u,exp v) converges uniformly to
  exp(-2(u+v)) on each closed nonnegative rectangle. Likewise
  q^(-2) C_3,T(B^r,exp s) converges uniformly to r(1+s)exp(-2s) on
  [r0,r1] x [0,S], where 0<r0<=r1<1 and S>=0. Coordinate exchange gives
  the other axis. These uniform profiles require no test function and
  include s=0. Every compact subset of the stated domains fits such a box.

All inherited analytic constants remain existential. The historical
numerical-effectiveness assertions are not promoted. No RH, simplicity,
critical-line substitution, signed-sector assembly, kernel removal or
ordinate-only conclusion is introduced. The unresolved signed complex-argument
error remains unresolved.

## Proof organization and audit

`TripleBoundaryAssembly` imports the complete development. The machine-readable
inventory lists 51 modules and all 143 public declarations. The challenge
imports project definitions only, with an independent expected statement for
every public theorem. Six unfinished-proof controls target the interchange,
integrated budget, origin profile, axis profile, quadrant limit and distributional
Fourier passage. Permitted axioms are only propext, Quot.sound and Classical.choice.

Named estimates and continuous majorants precede their integration. The actual
residual is measurable through the full frequency identity and the continuous
retained main term; no measurability of separately split arithmetic errors is
presupposed. A useful checked simplification is H_total(T,x)<=H_constant/x
for 1<=x<=T, including the pole term. It improves the integrated H-word route
without changing the exact signed accounting. The local profile proof retains
L^2/(XY) in the residual; a bound uniform but constant in XY would lose the
nonzero-axis limit.

Reproduce with prepared dependencies:

```
python3 scripts/reproduce_lean.py --reuse-dependencies --triple-boundary-only
```

This mode skips dependency resolution and older Comparator suites, while
retaining the complete project build, complete axiom report, analytic-coverage
checks, and pair/triple/harness regressions. No proof is supplied by Python.
