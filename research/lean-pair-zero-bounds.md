# Uniform pair zero-side errors

Assumptions: `UNCONDITIONAL`. Ledger: `PAIR-ZERO-BOUNDS-FORMAL-001`.

## Checked statement

Use the vectors and errors from [the exact decomposition](lean-pair-zero.md).
All sums count actual zero occurrences with analytic multiplicities. Define

\[
 B(Z)=\max\bigl(\{0\}\cup\{\beta_i-\tfrac12:|\gamma_i|\le Z\}\bigr).
\]

Lean proves `0 ≤ B(Z) < 1/2`, `|βᵢ−1/2| ≤ B(Z)` on the cutoff by
reflection, and `B(Z)=0` for an empty cutoff. The constant zero in the maximum
makes this definition meaningful for every real Z.

There exist **absolute positive constants** \(C_{tr},C_h,C_e\), chosen before
all parameters, such that for every real \(X\ge1,T\ge3,Z\ge2T\),

\[
\begin{aligned}
 |E_{\rm trunc}|&\le C_{tr}XT\left(
 \frac{\log(T+2)\log Z}{Z}+\frac{\log^2 Z}{Z^2}\right),\\
 |E_{\rm trunc}|&\le C_{tr}XT\frac{\log^2 Z}{Z},\\
 |E_{\rm height}|&\le C_h X^{2B(Z)}\log^3 T,\\
 |E_{\rm extension}|&\le C_e X^{2B(Z)}\log^2 T,
 \qquad E_{\rm extension}\le0.
\end{aligned}
\]

The same constants work with B(Z) replaced by **any** larger real b in the
last two bounds. `pairZeroUniformBounds` and
`pairZeroUniformBounds_envelope` state these quantified conclusions.
The refined truncation bound retains the quadratic remainder.

The constants are existential, inherited from the checked kernel/counting
estimates. This milestone makes no new numerical effectivity claim.

## Proof and dependency table

Write \(k(v)=(1+v^2)^{-1}\), \(w=X^{B(Z)}\), and \(R=U-U_Z\).
The scalar denominator has norm at least \(\frac34(1+v^2)\); hence
\(\|v_i(t)\|\le\frac43 X^b k(t-\gamma_i)\) whenever \(\delta_i\le b\).

| Component | Checked mechanism | Uniformity / interchange |
| --- | --- | --- |
| Envelope | Finite maximum, ordinary critical strip, occurrence reflection | Every real Z; empty cutoff included |
| Full vector | Global kernel bound and \(\delta_i\le1/2\) | \(\|U\|\ll X^{1/2}\log(T+2)\) on [0,T] |
| Truncation remainder | Complementary absolutely convergent occurrence sum; distant-kernel bound | \(\|R\|\ll X^{1/2}\log Z/Z\) for **Z≥2T**, including t=T |
| Squared truncation | \(\bigl|\|U\|^2-\|U_Z\|^2\bigr|\le2\|U\|\|R\|+\|R\|^2\) | Constant majorant integrated over length T |
| Height replacement | Finite set difference of cutoff and (0,T]; exterior-kernel bound | Only retained occurrences receive the finite-envelope weight |
| Boundary integral | Primitive \(\log(1+t)-\log(1+T-t)\) | Integral of \((1+t)^{-1}+(1+T-t)^{-1}\) equals \(2\log(1+T)\) |
| Extension | Interior-kernel bound outside [0,T], squared | \(\|V(t)\|^2\ll w^2\log^2(T+2)(1+d(t,[0,T]))^{-2}\) |
| Exterior integral | Improper primitive \(-(1+t-a)^{-1}\); reflection for the left tail | Integrability proved first; each tail has integral 1, total 2 |
| Final logarithms | `pairRHS_log_comparison` | \(\log(T+2)\le2\log T\), T≥3 |

The finite-window difference is bounded by the positive exterior kernel sum.
It does not assign the finite-height envelope to occurrences outside the cutoff.
No infinite double zero sum is integrated. The only infinite vector subtraction
uses absolute convergence; the integrals of the named errors already have
integrability proofs in the exact-decomposition milestone. Boundary majorants
have their own integrability proofs before integral comparison.

For example, if G,D,E are the existing global, distant and exterior kernel
constants, the proof uses A=4G/3, B=4D/3 and truncation constant
\(4(2AB+B^2)\). The height constant is
\(64\cdot2(4/3)^2GE\); the extension constant is
\(32(4I/3)^2\), where I is the interior kernel constant.
The consolidated theorem can enlarge the truncation constant to serve both
forms simultaneously. These formulas do not turn existential inputs into
numerically evaluated constants.

## Endpoints and assumption audit

- X=1, T=3 and Z=2T are included literally; no strict version is substituted.
- Cutoff: \(|\gamma|\le Z\). Window: \(0<\gamma\le T\). Every endpoint
  occurrence and multiplicity is retained. Distinct complex zeros at a common
  ordinate remain distinct summands.
- Extension integrates over the complement of [0,T]; switching open/closed
  endpoints in profile integrals uses Lebesgue null singletons only.
- Reflection negates displacement and preserves ordinate and multiplicity.
- The envelope proof uses only \(0<\beta<1\); no \(\beta=1/2\)
  substitution or new zero-free-region theorem is used.
- This milestone has no varying-parameter limit or limit-order assertion.
  Every bound is simultaneous in its stated real parameters.

## Verification

`research/lean-pair-zero-bounds-inventory.json` lists all **33** public declarations.
Every declaration has a definition-only Comparator challenge and an axiom report.
The unfinished consolidated theorem is a negative control and must be rejected
for `sorryAx`. Only `propext`, `Quot.sound`, and `Classical.choice` are allowed.
Nanoda is disabled; this is Lean/Comparator verification, not a second-kernel
certificate. The combined project build, complete axiom report, coverage checks,
and pair/triple regression suites are included in the focused run:

```sh
python3 -B scripts/reproduce_lean.py --skip-bootstrap --pair-zero-bounds-only
```

This mode uses already prepared, pinned dependencies. The ordinary full runner
also includes this suite. Content-addressed evidence is referenced by the ledger;
earlier Comparator suites are not rerun by the focused mode.

## Next boundary

The cutoff optimization, small-height absorption, and uniform comparison are now
checked in [the comparison milestone](lean-pair-zero-comparison.md), using the
already verified PREPRINT strip input. The historical `PAIR-TRUNC-001` remains
partial because its effective-constant assertion is separate; the original KV
comparison route also remains incompletely formalized. The comparison and RHS
mean square are now assembled in the [normalized pair theorem](lean-pair-asymptotic.md).
The older explicit norm-tail constant and signed triple complex-argument o(1)
error remain separate obligations.
