# Uniform triple error budget and additive limit

Task: formal verification. Assumptions: `UNCONDITIONAL`.

The formalization retains the full-zero master observable, all multiplicities,
and the exact retained expression

\[
M_T=(\log T)^3/(XY)^2+J_1D(X,XY)/Y+J_1D(Y,XY)/X-R_{\rm res}(X,Y).
\]

`tripleBudget_uniform_asymptotic` chooses one absolute existential constant
before the smooth nonnegative mass-one weight, its supremum bound `W`, the
margin, height, and prime scales. For topological support inside `(1,2)`,
`T >= 3`, `0 < epsilon < 1/3`, `T^epsilon <= X,Y` and
`XY <= T^(1-epsilon)`, it proves

\[
|C_{3,T}-M_T|\le C(1+W+\|\omega'\|_1)T^{-\epsilon}\log(2T+2)^4.
\]

Any nonnegative uniform upper bound `W` for the weight is accepted, so the
statement applies in particular to its supremum norm. The constant is
existential through the pair mean-square input; no numerical-effectiveness
claim is added. `tripleBudget_uniform_additive_limit` proves uniform additive
`o(1)` over the moving parameter range with fixed weight and positive margin.
It does not prove a relative error, a varying-margin limit, a general
three-level test-function theorem, or removal of complex test arguments.

The checked components include:

- The exact eight-error plus nineteen-word signed budget and its 208 ordered
  remainder refinements, counted once.
- Compact logarithmic weight smoothness, endpoint vanishing through zero
  extension, moment bounds, derivative L1 bounds and normalized Fourier scaling.
- The absolute ordered reciprocal-log bound with constant `4 sqrt(2)`;
  comparable-ratio boundaries are included and equal integers excluded.
- Prime coefficient masses, the exact closed mass constant, mixed diagonal
  bounds, a mean-square norm branch including `x=2T`, and all four remainders.
- Ordered convolution grouping, its mass and fifth-logarithmic energy, and
  identification of its exact diagonal with the prime-power resonance mass.
- Both mixed off-diagonal rates and the cubic rate for every `X,Y >= 1`;
  these do not require `XY <= 2T`. The mixed logarithmic factor is written
  as `sqrt(ell_x^3 ell_z^3)`.
- Bounds for the four nonresonant archimedean words and the nineteen remainder
  words. The latter depend only linearly on the smoothing supremum bound.

The two-branch norm envelope is separate from coarse bounds expressed using
actual weighted L2 norms and masses. The one-prime bound uses the stronger
constant five. Historical ledger claims retain their existing statuses;
coverage records the effective-constant and packaging qualifications.
The signed complex-argument error for an ordinate-only statistic remains open.

Verification uses 219 public statement comparisons against a definition-only
challenge, six separate rejected unfinished-proof controls, the combined
project build and full axiom report. Allowed axioms are `propext`, `Quot.sound`
and `Classical.choice`; the external kernel is disabled.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-budget-only
```

The focused mode reuses the pinned dependencies and does not rerun earlier
Comparator suites. Its content-addressed manifest records actual outcomes;
Python coverage checks are bookkeeping, not analytic certificates.
