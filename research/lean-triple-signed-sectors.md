# Signed frequency sectors and smooth tests: Lean verification

Task: formal verification. Assumptions: `UNCONDITIONAL` and
`SUPPORT(compact subset of max(abs(xi),abs(eta),abs(xi+eta))<1)`.

The milestone is complete. The focused reproduction passed all 84 statement
comparisons across 19 modules, six rejected unfinished-proof controls, the
combined build, complete axiom report, coverage, harness and pair/triple
regressions. The formal ledger entry is `MASTER-SIGNED-SECTORS-FORMAL-001`.

Certificate: [PASS manifest](../artifacts/certificates/lean/9bb0d8a231766ad5f7448cf57f9770ffc515114c31df691f16dcf08c8331fd21/manifest.json).
All Lean source and challenge hashes match the certified run. Subsequent
ledger, coverage and documentation updates record this result without changing
proof sources or extending the historical RH-audit scope.

The development extends the actual zero series and master identity to positive
bases, uses multiplicity-preserving horizontal reflection for reciprocal
conjugation, and partitions the plane into the six archived determinant-one
sectors. The horizontal coefficient is bounded by B^h after collecting the
anchor displacement. A uniform integral-norm majorant justifies the full-zero
sum/integral interchange for integrable amplitudes supported in h<=1-kappa.

Smooth complex tests pull back with conjugation on the three negative sectors.
The checked assembled limit is (3/2) phi(0,0) plus (3/2) times the integral of
|r| [phi(r,0)+phi(0,r)+phi(r,-r)] dr. The diagonal uses dr, not arclength.
The C1 seminorm is the sum of the three global suprema; each quadrant seminorm
is at most twice this value. The uniform error is
C ||phi||_C1 (1+W+||omega'||_1) (1/log B+B^(-kappa) log(2T+2)^3).

The exact identity has factor 8/log T and anchor permutation (i2,i3,i1).
It retains the horizontal kernel and complex arguments, all ordered actual
zero occurrences, multiplicities, both ordinate signs, and partial diagonals.
Independent occurrence cutoffs are removed at fixed parameters before the
height limit. The inverse Fourier transform is entire and its real restriction
is Schwartz in the project's 2pi convention.

All inherited analytic constants remain existential. Historical numerical
effectiveness assertions retain their existing status. The outer boundary
h=1, kernel removal, ordinate-only statistics and the unresolved signed
complex-argument error are outside this milestone.

Reproduce with:

```sh
python3 scripts/reproduce_lean.py --reuse-dependencies --triple-signed-sectors-only
```

The focused suite compares every public declaration with definition-only
expected statements, rejects unfinished proofs for reflection, interchange,
support, conjugation, normalization and the limit, then checks the combined
build, complete axiom report, coverage, harness and pair/triple regressions.
Only propext, Quot.sound and Classical.choice are permitted.
