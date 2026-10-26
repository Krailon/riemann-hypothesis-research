# Sharp first smoothing moment

Task: formal verification. Assumptions: `UNCONDITIONAL`.

For the existing `TripleBudgetWeight` (smooth, nonnegative, supported inside
(1,2), and of integral one), define

\[
\mu_\omega=\int_{\mathbb R}\omega(u)\log u\,du
          =\int_1^2\omega(u)\log u\,du.
\]

`tripleSmoothingMoment_sharp` proves, including T=3,

\[
0\le\mu_\omega\le\log2,\qquad
0\le J_1-\log T-\mu_\omega\le 2/T.
\]

`tripleSmoothingError_bounds` actually holds for every T>0, uniformly over
all admissible weights. The constant two is explicit; no PNT, prime estimate,
zero-location premise or existential analytic constant is used.

The exact correction is

\[
J_1-\log T-\mu_\omega
 =\int_{\mathbb R}\omega(u)\log\!\left(1+\frac2{Tu}\right)\,du.
\]

The weighted logarithm is continuous and integrable: off the topological
support the weight vanishes locally, including near zero. The correction
integrand is integrable by identification with a difference of three already
integrable functions. Integral splitting therefore follows integrability,
and the pointwise identity is used only on the support, where 1<=u<=2.
There the correction logarithm lies between zero and 2/T. Nonnegativity and
unit mass transfer these bounds to the integral.

The manuscript mean uses the ordinary interval integral on [1,2]; the endpoint
conventions agree because the weight is supported strictly inside (1,2).
`tripleSmoothingMoment_tendsto` proves J1-log T tends to the fixed mean as
T tends to infinity, by squeezing the remainder. It exchanges no limit with
an integral. The preceding explicit bound is uniform even when the admissible
weight varies with height, though the limit theorem fixes the weight.

Verification covers all 13 public declarations against an independent
challenge importing only project definitions, with two unfinished-proof
controls for the exact correction identity and the sharp bound. The combined
project build, complete axiom report and regressions run in the focused mode:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-smoothing-only
```

Allowed axioms are `propext`, `Quot.sound` and `Classical.choice`; the external
kernel is disabled. The runner archives actual results in a content-addressed
manifest. Python checks verify bookkeeping and harness behavior, not analysis.

This completes the smoothing-moment portion of `TRIPLE-RETAINED-001` alongside
the previously formalized mixed diagonal. Resonance decay and the assembled
retained-term evaluation remain separate. Historical ledger statuses and
RH-audit scopes are preserved; the signed complex-argument error remains open.
