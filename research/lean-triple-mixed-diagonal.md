# Uniform mixed-prime diagonal

Task: formal verification. Assumptions: `UNCONDITIONAL`.

For the existing actual coefficient series `tripleBudgetDiagonal a b`, the
formalization proves one absolute constant C>0 such that, for every 1<=a<=b,

\[
\left|D(a,b)-\frac{a}{2b}(1+\log(b/a))\log(ab)\right|
\le C\frac ab(1+\log(b/a)).
\]

The symmetric interface orders the arguments using min/max. All prime powers
remain present. No smoothing, height, Fourier-support or zero-location
hypothesis is needed for this arithmetic estimate. The proof reuses the checked
cumulative estimate |A(u)-u log u|<=K u, including proper prime powers and the
bounded range 1<=u<2. The exported conditional interface gives C=3K+1; the final
unconditional theorem discharges that premise. K, hence C, is existential
through the checked PNT input; no numerical effectiveness is claimed.

At finite Y>=b, the ranges are n<=a, a<n<=b, and b<n<=Y. The product weight is
u/(ab), a/(bu), and ab/u^3, respectively. Both internal boundary terms cancel
exactly. The finite model is

\[
\frac{a}{2b}(1+h)\log(ab)+\frac ab(1+h)-\frac1{4ab}
-\frac{ab(2\log Y+3)}{4Y^2},\qquad h=\log(b/a),
\]

with absolute error at most K(a/b)(3+h). Finite integrability is checked before
splitting errors. Absolute summability identifies the limit of the partial
sums, and the displayed upper boundary tends to zero with a,b fixed. Only then
is the uniform constant extracted. The endpoints a=1, a=b, a=b=1, and all
integer cutoffs (including primes and proper prime powers) are included. The
equal-scale specialization recovers D(a,a)=log a+O(1).

Verification covers all 28 public declarations against a definition-only
challenge, with three separate unfinished-proof rejection controls for the
finite identity, unconditional asymptotic, and integer endpoints. It includes
the combined project build, full axiom report and regression checks. Allowed
axioms are `propext`, `Quot.sound`, and `Classical.choice`; the external kernel
is disabled. Python checks verify bookkeeping, not the analytic argument.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-mixed-diagonal-only
```

The focused mode reuses pinned dependencies and skips earlier Comparator
suites. The runner archives actual outcomes in a content-addressed manifest.
This milestone covers only the mixed-diagonal part of `TRIPLE-RETAINED-001`;
the sharper smoothing moment, resonance decay, full retained-term evaluation,
and interior-vanishing theorem are separate tasks. Historical statuses and
RH-audit scopes are unchanged. The signed complex-argument error remains open.
