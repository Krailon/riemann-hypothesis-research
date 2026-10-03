# Explicit triple kernel and critical-line specialization

Task: proof and bookkeeping. The three claims below have status
**proved-draft**. Assumptions are `UNCONDITIONAL`, with the stated support
restriction for the correlation consequence. The final all-zero
critical-line interpretation is explicitly conditional on `RH` and is
not used in an unconditional proof. The [proof](../proofs/triple_explicit_formula.tex)
and [ledger](theorem-ledger.yaml) record the statements.

## 1. Full horizontal profile

Claim **TRIPLE-KERNEL-PROFILE-001**, label **lem:triple-kernel-profile**.
For the existing kernel \(K_T(j,k,\ell)\), define
\[
a=\gamma_j-\gamma_\ell,\quad b=\gamma_k-\gamma_\ell,\qquad
z_1=a-i\delta_j,\quad z_2=b-i\delta_k,\quad z_3=i\delta_\ell,
\quad d_{mn}=z_m-z_n.
\]
These \(z_m\) are integration centers, distinct from the scaled test
arguments \(z_{21},z_{31}\). The exact profile is
\[
\mathcal J(a,b;\delta_j,\delta_k,\delta_\ell)
=\int_{\mathbb R}\prod_{m=1}^3\frac{dv}{1+(v-z_m)^2}
=\pi\frac{24+d_{12}^2+d_{13}^2+d_{23}^2}
{(4+d_{12}^2)(4+d_{13}^2)(4+d_{23}^2)}.
\]
The domain is all real \(a,b\) and \(|\delta_m|\le1/2\), including
closed horizontal endpoints and all coincident-center cases. Each
upper pole is at least \(1/2\) above the real axis, and
\(\operatorname{Re}(4+d^2)\ge3+(\operatorname{Re}d)^2\), so the
final denominators never vanish.

For distinct centers, the residues give
\[
\mathcal J/\pi=\sum_{m=1}^3\prod_{n\ne m}
[d_{mn}(d_{mn}+2i)]^{-1}.
\]
The proof clears denominators, checks the resulting polynomial identity,
and uses dominated convergence to include collisions. One never evaluates
the singular separate-residue expression at a collision.
All derivatives are uniformly bounded on compact gap sets times the
closed horizontal cube. Exchange of the first two slots exchanges
\(a,b\) and their deltas. Negating all deltas conjugates \(\mathcal J\).
This is compatible with the existing full-zero reflection convention.

## 2. Height localization and named summable errors

Claim **TRIPLE-KERNEL-LOCALIZATION-001**, label
**lem:triple-kernel-localization**. Extend the existing smooth weight by
zero outside \((1,2)\). For \(T\ge3\),
\[
K_T(j,k,\ell)=\frac{\omega(\gamma_\ell/T)}T
\mathcal J(a,b;\boldsymbol\delta)+E_{\rm kernel}(j,k,\ell).
\]
Writing \(W_\infty=\|\omega\|_\infty\),
\(W'_\infty=\|\omega'\|_\infty\), and \(L=\log(2T+2)\), the tuplewise
bound is
\[
|E_{\rm kernel}(j,k,\ell)|
\le\frac{64\pi W'_\infty}{27T^2[4+(a-b)^2]}.
\]
It follows from the Lipschitz bound for the weight,
\(|v|/(1+v^2)\le1/2\), and the exact two-factor integral
\(2\pi/[4+(a-b)^2]\). **This tuplewise bound alone is not summed over
all triples.** The actual summed estimate is
\[
\sum_{j,k,\ell}|E_{\rm kernel}(j,k,\ell)|
\ll\frac{W'_\infty L^4+W_\infty L^3}{T}.
\]
Both signs of ordinates, multiplicities, and all five index patterns
are retained. Constants are effective and absolute.

Set \(v=t-\gamma_\ell\). Split each signed error integral into the
following disjoint pieces; elsewhere both weights vanish.

| Error | Integration region | Bound after summing absolute values over all triples |
| --- | --- | --- |
| \(E_{\rm kernel,near}\) | \(|v|\le T\) | \(O(W'_\infty L^4/T)\) |
| \(E_{\rm kernel,far\text{-}center}\) | \(|v|>T,\ t\in[T,2T]\) | \(O(W_\infty L^3/T)\) |
| \(E_{\rm kernel,far\text{-}anchor}\) | \(|v|>T,\ t\notin[T,2T],\ \gamma_\ell\in[T,2T]\) | \(O(W_\infty L^3/T)\) |

The proof uses \(Q(t)=\sum_j(1+(t-\gamma_j)^2)^{-1}\ll\log(|t|+2)\).
On the near part, a nonzero weight difference forces \(t\in[0,3T]\);
unit-shell counts bound the weighted anchor sum by \(O(L^2)\).
Distant shells give \(O(L/T)\) for anchors viewed from a center in
\([T,2T]\). For anchors in that interval, the distant integral of
\(Q(t)^2/(1+(t-\gamma_\ell)^2)\) is \(O(L^2/T)\), and there are
\(O(TL)\) anchors. Thus all tails are controlled before any cutoff
is removed. These inputs are **PAIR-COUNT-001** and
**PAIR-COUNT-KERNEL-001**.

The norm \(W'_\infty\) is new and remains distinct from the earlier
\(W_1=\|\omega'\|_1\). No derivative-norm substitution is implicit.

## 3. Unconditional correlation with the explicit profile

For the [signed-sector theorem](triple-test-functions.md), put
\(B=T/(2\pi),q=\log T\) and let \(\phi=\widehat F\) have compact
support in \(h\le1-\kappa\), where
\(h=\max(|\xi|,|\eta|,|\xi+\eta|)\) and \(0<\kappa<1\).
Define the absolutely convergent statistic
\[
\mathcal A_T^{\mathcal J}[\phi]
=\frac8{Tq}\sum_{i_1,i_2,i_3}
\omega(\gamma_{i_1}/T)
\mathcal J(\gamma_{i_2}-\gamma_{i_1},\gamma_{i_3}-\gamma_{i_1};
\delta_{i_2},\delta_{i_3},\delta_{i_1})F(z_{21},z_{31}).
\]
The arguments, conjugated anchor, all zero occurrences and partial
diagonals are unchanged. The compact-frequency representation gives
\(|F(z_{21},z_{31})|\le\|\phi\|_1B^{1-\kappa}\) for every triple.
Combined with the summed kernel error, this yields, for \(T\ge2\pi e\),
\[
|\mathcal A_T[\phi]-\mathcal A_T^{\mathcal J}[\phi]|
\ll\|\phi\|_1(W_\infty+W'_\infty)B^{-\kappa}L^3.
\]
Thus the explicit-profile statistic inherits the existing main term
\[
\frac32\phi(0,0)+\frac32\int_{\mathbb R}|r|
[\phi(r,0)+\phi(0,r)+\phi(r,-r)]\,dr.
\]
Its error is the sum of the existing signed-test error and this new
kernel error. The support region is unchanged. Absolute summability
follows first for \(\omega(\gamma_\ell/T)\mathcal J/T\) from the
original kernel bound and the summed difference; multiplication by the
uniform test bound then proves it for the displayed statistic.

All sums and interchanges are justified at fixed parameters. Fix test,
support margin and smoothing before \(T\to\infty\). For varying families,
both the old error and the new error must tend to zero.

## 4. Microscopic and critical-line formulas

Claim **TRIPLE-KERNEL-CRITICAL-SPECIALIZATION-001**, label
**cor:triple-kernel-critical**. Define
\[
h_{12}=\delta_j-\delta_k,\quad h_{13}=\delta_j+\delta_\ell,
\quad h_{23}=\delta_k+\delta_\ell.
\]
The unconditional zero-gap profile is
\[
\mathcal J(0,0;\boldsymbol\delta)
=\pi\frac{24-h_{12}^2-h_{13}^2-h_{23}^2}
{(4-h_{12}^2)(4-h_{13}^2)(4-h_{23}^2)}.
\]
For fixed \(R>0\), uniformly for \(|u|,|v|\le R\) and the closed
horizontal cube,
\[
\mathcal J(u/L_T,v/L_T;\boldsymbol\delta)
=\mathcal J(0,0;\boldsymbol\delta)+O_R(L_T^{-1}).
\]
No convergence of the deltas is assumed. Together with height
localization, the tuplewise kernel error is
\(O_R(W_\infty/(TL_T)+W'_\infty/T^2)\).

**Critical-line parameter specialization:** set all three deltas to zero.
Then
\[
\mathcal J(a,b;\mathbf0)=\pi
\frac{24+a^2+b^2+(a-b)^2}
{(4+a^2)(4+b^2)(4+(a-b)^2)},
\]
\[
\mathcal J(u/L_T,v/L_T;\mathbf0)
=\frac{3\pi}{8}-\frac{5\pi}{32L_T^2}(u^2+v^2-uv)
+O_R(L_T^{-4}).
\]
For a critical-line tuple with these bounded scaled gaps,
\[
K_T(j,k,\ell)=\frac{3\pi}{8T}\omega(\gamma_\ell/T)
+O_R\left(\frac{W_\infty}{TL_T^2}+\frac{W'_\infty}{T^2}\right).
\]
All constants are effective; fix \(R\) before the microscopic limit.
The horizontal profile is not constant: at algebraic parameters with
all deltas equal to \(d\), it is \(\pi(3-d^2)/(8(1-d^2)^2)\),
which at \(d=1/4\) equals \(94\pi/225\). This parameter example does
not assert the existence of an off-line zeta zero.

The exact normalization comparison is
\[
\frac8{T\log T}\frac{3\pi}{8}
=\frac{3\log(T/2\pi)}{2\log T}\frac1{TL_T}.
\]
The coefficient relative to \((TL_T)^{-1}\) tends to \(3/2\).
This accounts for the local critical-line normalization. The subsequent
[main-term comparison](triple-main-term-comparison.md) identifies the full
limiting functional as three halves of the all-ordered sine benchmark.

| Statement | Assumption and scope |
| --- | --- |
| Rational profile and summed height-localization error | `UNCONDITIONAL`, full zeros and horizontal dependence |
| Explicit-profile correlation | `UNCONDITIONAL`, stated open-hexagon support margin |
| Kernel evaluated at three zero deltas | `UNCONDITIONAL` parameter specialization; applies to tuples already known to lie on the line |
| All zero tuples have three zero deltas | `RH`; conditional interpretation only, unused in preceding claims |
| Replace the profile everywhere by \(3\pi/8\) | Not established, even by the local critical-line expansion |

The next missing ingredient for constant-kernel replacement is a summed
microscopic error and tail estimate. Unconditionally, Schwartz decay on
the real plane alone cannot localize the complex test arguments. The
proved full-gap profile replacement already preserves the main term;
further kernel removal and horizontal extraction remain separate tasks.
Main-term identification is now supplied by the comparison lemma.

## 5. Verification and provenance

Run the [exact kernel checks](../scripts/check_triple_kernel.py) through
standard triple-suite discovery:

```bash
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py' -v
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v
```

Validation on 2026-10-02: all 71 triple checks, including eleven new
kernel checks, and all 70 pair checks passed. The expanded 29-page proof
compiled with shell escape disabled and no final-pass warnings,
unresolved references, or overfull/underfull boxes.

The new checks verify the cleared-denominator residue identity as an
exact bivariate polynomial, generic complex residues, collisions and
horizontal endpoints, full-zero denominator translation, symmetries,
the two-factor integral and tuplewise constant, disjoint near/far
regions, dyadic tail moments, the horizontal profile, critical-line
Taylor coefficients and the exact normalization. Computation is finite
verification, not an analytic proof or numerical certificate.

The pair-audit ledger hash was refreshed only after checking that the
previous ledger is an unchanged byte prefix followed by the three new
claims. Existing claim statements, audit snapshot, audited pair proof
and Work Package A archive remain unchanged. That audit's coverage has
not been extended to these Work Package B claims.
