# Integral profile and horizontal derivatives

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
This milestone continues the [rational-transfer formalization](lean-rational-transfer.md).

**Verified:** the fresh-project run on 2026-10-11 UTC passed
**82 new Comparator specifications**, all earlier proof checks, **seven
unfinished-proof negative controls**, **285 distinct axiom reports**,
**196 pair/triple regressions**, and **13 coverage-map checks**. The
[complete verification archive](../artifacts/certificates/lean/f2907d4ab8fcb06157fdfcf2daa35276de87bfa7005ee93758aecb5a3d3003f7/manifest.json)
records source hashes, tool pins, logs, and dependency compatibility patches.

The subsequent [uniform-height milestone](lean-uniform-height.md) proves
logarithmic local counts, uniform rational ordinate-kernel sums, global
anchored triple counts and normalized real-test tails. References below
to those remaining tasks describe this earlier milestone. The stronger
pair-dependent near count and signed `o(1)` remain open.

## Exact statement and conventions

For real a,b,e,f,g set

\[
 k(x,e)=\frac1{1+(x+ie)^2},\qquad
 J_{\mathrm{int}}(a,b;e,f,g)
 =\int_{\mathbb R} k(t-a,e)k(t-b,f)k(t,-g)\,dt.
\]

The third factor has **−g**. Its center is **+ig**, while the first two
centers are a−ie and b−if. The gaps a,b are unscaled ordinate differences.
There is no Fourier normalization change.

Lean proves absolute Bochner integrability and equality with

\[
 J=\pi\frac{24+d_{12}^2+d_{13}^2+d_{23}^2}
 {(4+d_{12}^2)(4+d_{13}^2)(4+d_{23}^2)},\quad
 d_{mn}=c_m-c_n,\quad (c_1,c_2,c_3)=(a-ie,b-if,ig)
\]

on the enlarged **closed cube |e|,|f|,|g|≤3/4**, for every real a,b.
All coincident centers and parameter endpoints are included. On the required
closed half cube, the integral is smooth in **all five real parameters** in a
neighborhood of each point. The earlier rational-profile identities therefore
apply to the integral, including partner exchange, conjugation under simultaneous
horizontal sign reversal, and the coincident value J(0,0;e,e,−e)=3π/8 for |e|≤3/4.

## Absolute convergence and finite-interval evaluation

The checked scalar estimate is

\[
 |1+(x+ie)^2|\ge\tfrac7{16}(1+x^2),\qquad
 |k(x,e)|\le\frac4{1+x^2}\quad(|e|\le3/4).
\]

Bound the first two factors by 4 and retain the anchor's decay. This yields
**64/(1+t²)**, integrable on the whole line and independent of a,b,e,f,g in
the stated domain. It supplies both absolute integrability and dominated
continuity in the real gaps.

For distinct centers, index the six poles p by (m,sign), with p=c_m±i.
Their imaginary parts have the indicated signs and absolute value at least 1/4.
The Lagrange-basis identity gives the exact finite partial fraction expansion

\[
 \frac1{\prod_p(z-p)}=\sum_p\frac{A_p}{z-p},\qquad
 A_p=\prod_{q\ne p}(p-q)^{-1}.
\]

Every term is integrated on **[−R,R] first**. The imported finite-interval
logarithm/arctangent identity implies, for p off the real axis,

\[
 \lim_{R\to\infty}\int_{-R}^{R}\frac{dt}{t-p}
 =\begin{cases}i\pi&\Im p>0,\\-i\pi&\Im p<0.\end{cases}
\]

Lean checks the logarithm difference tends to zero by normalizing its quadratic
ratio to a limit of 1, and checks both arctangent endpoint signs. An individual
simple pole is **not** assigned a whole-line Lebesgue integral. Only the full
product is absolutely integrable. Its symmetric truncations converge to its
Bochner integral; uniqueness of limits identifies that integral with the
finite sum of pole limits. The six coefficients simplify to the displayed J.

Collision extension uses a+ε,b+2ε, excluding the finite real set
{−a,−b/2,a−b}. Its complement is dense. Dominated continuity of the integral
and continuity of the nonsingular rational formula give equality at ε=0.
No limiting partial-fraction coefficient is evaluated at a collision.

**Limit order:** fix all parameters, integrate the finite partial fraction
identity, send R→∞, and then extend to collisions by continuity. No zero sum,
Fourier integral, or height limit is interchanged in this calculation.

### Imported input and axiom boundary

The only imported integration formula beyond mathlib is
`integral_const_div_self_add_im` in
`PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean`, at the existing pinned
PrimeNumberTheoremAnd revision **c39a751132c88b6e8080b74c74023fd95b3d8be0**.
It evaluates a finite interval integral A/(x+iy) for real y≠0. Its proof is
complete. Later residue-theorem scaffolding in that source file is not used.
The reproduction harness prints this imported declaration's axioms separately,
as well as those of every new public project theorem. The permitted axioms
remain `propext`, `Quot.sound`, and `Classical.choice`; the external kernel
remains disabled. Dependency pins and compatibility patches are unchanged.

## Mixed horizontal derivatives

For each natural n the scalar jet is defined explicitly by

\[
 k_n(x,e)=\frac{(-i)^n n!}{2i}
 \left((x+ie-i)^{-n-1}-(x+ie+i)^{-n-1}\right).
\]

Lean proves k₀=k, ∂ₑkₙ=kₙ₊₁, and

\[
 |k_n(x,e)|\le\frac{4^{n+1}n!}{1+x^2}\quad(|e|\le3/4).
\]

An ordered list of coordinates defines a mixed partial. If its three counts
are r,s,u and its length is n, its integrand is

\[
 k_r(t-a,e)\,k_s(t-b,f)\,(-1)^u k_u(t,-g).
\]

The anchor contributes exactly (−1)ᵘ. The product of factorials is at most n!,
and the scalar bounds give the uniform majorant

\[
 \frac{4^{n+3}n!}{1+t^2}.
\]

The derivative's continuous-linear-map norm is dominated by
3·4ⁿ⁺⁴(n+1)!/(1+t²). These explicit bounds justify differentiation under the
integral on the open enlarged cube. Induction identifies the resulting
integrals with the iterated Fréchet coordinate derivatives of J. Consequently,
on the closed half cube,

\[
 |\partial^\alpha J|\le C_n:=4^{n+3}n!\pi,\qquad n=|\alpha|.
\]

The proof works for **every natural order**, including the requested orders
through four. The constants are independent of both real gaps.

| Order n | Cₙ |
| --- | --- |
| 0 | 64π |
| 1 | 256π |
| 2 | 2048π |
| 3 | 24576π |
| 4 | 393216π |

For n=0 the earlier 7π/9 bound is sharper. These derivative constants are
explicit safe bounds, with no optimality claim.

## Directional and symmetric remainders

Write δ=(e,f,g), S=|e|+|f|+|g| and G(t)=J(a,b;te,tf,tg).
For |δⱼ|≤1/2 and |t|≤1, Lean proves

\[
 |G^{(n)}(t)|\le C_n S^n.
\]

Taylor's integral remainder on [0,1] is applied to δ and −δ. The initial
jets change by (−1)ⁿ, so the odd terms cancel. The resulting checked estimates are

\[
 \left|\frac{G(1)+G(-1)}2-G(0)\right|
 \le\frac{C_2}2 S^2=1024\pi S^2,
\]
\[
 \left|\frac{G(1)+G(-1)}2-G(0)-\frac{G''(0)}2\right|
 \le\frac{C_4}{24}S^4=16384\pi S^4.
\]

These are complex norm inequalities. No reality or sign of J is assumed.
Simultaneous sign averaging is a local kernel operation; it does not assert
cancellation for the full complex-test statistic.

## Actual occurrences and verification scope

For a tuple t:Fin 3→ZeroOccurrence, slot 0 remains the anchor. Substitute

\[
 a=\gamma_1-\gamma_0,\quad b=\gamma_2-\gamma_0,\quad
 (e,f,g)=(\delta_1,\delta_2,\delta_0).
\]

The existing proved displacement bound supplies the closed half-cube hypotheses.
`actualRationalKernel_integral` identifies the actual kernel with its absolutely
convergent integral. Separate checked declarations specialize every ordered
mixed derivative and both symmetric remainder estimates. There is no
restriction on ordinate signs, multiplicities, equal ordinates or equal complex
zeros. These pointwise statements introduce no new zero-sum interchange.

The [inventory](lean-integral-profile-inventory.json) lists **82 public theorems**
in twelve solution modules. Each has a definition-only Comparator specification
and axiom report. An unfinished version of `integralProfile_eq` is a negative
control and must fail for `sorryAx`. Intentional unfinished proofs occur only in
the challenge and negative-control modules, never in the solution modules.

```bash
python3 -B scripts/reproduce_lean.py --fresh-project
python3 -B scripts/check_lean_analytic_coverage.py
```

The coverage map retains the 46 historical nodes and 92 edges, with 220 component
records. Historical ledger blocks, RH-audit snapshots and archived baselines
retain their original scope. The profile's analytic statement is now covered
by the integral, smoothness and earlier symmetry components; the original
contour-residue proof and its master-formula dependency are not formalized.
New ledger entries record the exact standalone statements proved here.

## Remaining work

The next analytic prerequisites are sharper local zero counts and uniform
height estimates, followed by the explicit-formula and prime-side dependency
graph. This milestone does not prove a signed complex-argument o(1), remove
its horizontal test arguments, or establish a conventional ordinate-only
three-level asymptotic.
