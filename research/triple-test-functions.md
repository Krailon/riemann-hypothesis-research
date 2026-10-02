# Retained terms and the interior weighted test-function theorem

Task: proof and exposition. Assumptions: **UNCONDITIONAL**, with the
explicit Fourier-support restriction below for the test-function theorem.
All three new claims have status **proved-draft** in the
[ledger](theorem-ledger.yaml). The [proof](../proofs/triple_explicit_formula.tex)
retains the full zero coordinates and the master kernel.

## 1. Evaluating the retained terms

Claim **TRIPLE-RETAINED-001**, label **lem:triple-retained**.
Let \(q=\log T\), \(L=\log(2T+2)\), \(Z=XY\), and \(\ell_Z=\log(2Z)\).
The existing normalized nonnegative smoothing satisfies
\[
\mu_\omega=\int_1^2\omega(u)\log u\,du,\qquad
0\le\mu_\omega\le\log2,\qquad
0\le J_1-q-\mu_\omega\le2/T.
\]
Uniformly for \(1\le a\le b\),
\[
D(a,b)=\frac{a}{2b}(1+\log(b/a))\log(ab)
       +O((a/b)(1+\log(b/a))).
\]
Reverse arguments by symmetry. The proof uses **PRIME-PNT-001** to
establish \(\sum_{n\le u}\Lambda(n)^2=u\log u+O(u)\), including proper
prime powers, then integrates against the continuous weight
\[
w_{a,b}(u)=
\begin{cases}
u/(ab),&1\le u\le a,\\
a/(bu),&a<u\le b,\\
ab/u^3,&u>b.
\end{cases}
\]
Continuity handles prime-power endpoints without jumps. The cases
\(a=1\), \(a=b\) are included; the equal-base formula recovers
\(D(a,a)=\log a+O(1)\).

The cubic resonance is supported on proper prime powers. The elementary
bound \(N_{\rm pp}(u)\ll\sqrt u\) for their count, the ordered convolution
coefficient \((k-1)(\log p)^2\) at \(p^k\), and dyadic summation give
\[
0\le R_{\rm res}(X,Y)\ll Z^{-1/2}\ell_Z^3.
\]
This is a decaying bound, not a leading-term evaluation of the resonance.
No prime-power term is silently discarded.

Set
\[
G(X,Y)=\frac{(1+\log Y)\log(XZ)}{2Y^2}
       +\frac{(1+\log X)\log(YZ)}{2X^2}.
\]
If \(\Delta(a,b)\) is the remainder in the displayed mixed-diagonal formula,
the exact decomposition of the previously retained expression is
\[
M_T=q^3/Z^2+(q+\mu_\omega)G+E_D+E_J-R_{\rm res},
\]
where the newly named evaluation errors are:

| Error | Exact definition | Bound |
| --- | --- | --- |
| \(E_D\) | \(J_1(\Delta(X,Z)/Y+\Delta(Y,Z)/X)\) | \(O(L((1+\log Y)/Y^2+(1+\log X)/X^2))\) |
| \(E_J\) | \((J_1-q-\mu_\omega)G\) | \(0\le E_J\le2G/T\) |
| Resonance contribution | \(-R_{\rm res}\) | \(O(Z^{-1/2}\ell_Z^3)\) in absolute value |

These errors refine \(M_T\). They are not additional terms if \(M_T\) is
left intact in the [existing budget](triple-error-budget.md).
All constants are effective and absolute, and these evaluations do not
claim relative precision.

## 2. The interior limit is zero

Claim **TRIPLE-INTERIOR-VANISHING-001**, label
**cor:triple-interior-vanishing**. On
\[
0<\varepsilon<1/3,\quad T\ge3,\quad
T^\varepsilon\le X,Y,\quad XY\le T^{1-\varepsilon},
\]
the retained terms satisfy \(|M_T|\ll T^{-\varepsilon}L^3\).
Combining this with **TRIPLE-SMOOTHED-ADDITIVE-001** yields
\[
|\mathcal C_{3,T}(X,Y)|
\ll (1+\|\omega\|_\infty+\|\omega'\|_1)T^{-\varepsilon}L^4.
\]
Constants are independent of epsilon. The archimedean term is bounded by
\(T^{-4\varepsilon}L^3\), the mixed terms by \(O(T^{-2\varepsilon}L^3)\),
and the resonance by \(O(T^{-\varepsilon}L^3)\).
Thus the current interior observable tends uniformly to zero for fixed
epsilon and smoothing. This is not a relative asymptotic.

## 3. Fourier class, scaling, and zero-side observable

Claim **TRIPLE-TEST-FUNCTION-001**, label **thm:triple-test-function**.
Take arbitrary complex \(\phi\in C_c^\infty(\Omega_+)\), where
\[
\Omega_+=\{(\xi,\eta):\xi>0,\ \eta>0,\ \xi+\eta<1\}.
\]
Define the entire extension
\[
F(z_1,z_2)=\int_{\mathbb R^2}\phi(\xi,\eta)
                  e^{2\pi i(\xi z_1+\eta z_2)}\,d\xi\,d\eta.
\]
On the real plane \(F\) is Schwartz and \(\widehat F=\phi\) with the
project's negative-sign forward Fourier transform.
Choose \(0<\varepsilon<1/3\) such that
\[
\operatorname{supp}\phi\subset\Omega_\varepsilon
=\{\xi\ge\varepsilon,\ \eta\ge\varepsilon,\ \xi+\eta\le1-\varepsilon\}.
\]
Every compact subset of \(\Omega_+\) has such a margin. A nonzero smooth
bump supported in \([3/16,5/16]^2\subset\Omega_{1/8}\) shows that the class
is nonempty. Complex test functions are permitted; reality and positivity
are not imposed on this single positive-frequency class.

For \(T>2\pi\) use the following exact convention table.

| Object | Definition or convention |
| --- | --- |
| Exponential base | \(B=T/(2\pi)>1\) |
| Local spacing | \(L_T=\log B/(2\pi)\) |
| Prime bases | \(X=B^\xi,\ Y=B^\eta,\ Z=B^{\xi+\eta}\) |
| First complex argument | \(z_{21}=L_T((\gamma_{i_2}-\gamma_{i_1})-i(\delta_{i_2}+\delta_{i_1}))\) |
| Second complex argument | \(z_{31}=L_T((\gamma_{i_3}-\gamma_{i_1})-i(\delta_{i_3}+\delta_{i_1}))\) |
| Anchor and kernel | \(K_T(i_2,i_3,i_1)\): slot \(i_1\) is conjugated |
| Fourier phase | \(e^{2\pi i(\xi z_{21}+\eta z_{31})}\) |
| Normalization | Factor \(8\); \(1/T\) is already in \(K_T\). No additional \(L_T^2\), \(T\), or zero-count normalization. |
| Zero tuples | All ordered occurrences in the full zero multiset, both ordinate signs, full multiplicity, including all five index patterns. |

Then the weighted correlation is exactly
\[
\mathcal R^K_{3,T}[F;\omega]
=8\sum_{i_1,i_2,i_3}K_T(i_2,i_3,i_1)F(z_{21},z_{31})
=\int_{\mathbb R^2}\phi(\xi,\eta)
       \mathcal C_{3,T}(B^\xi,B^\eta)\,d\xi\,d\eta .
\]
The imaginary shifts retain horizontal information: with
\(x_\rho=\delta_\rho\log T\), the first is
\(-L_T(x_{\rho_{i_2}}+x_{\rho_{i_1}})/\log T\), and similarly for the second.
This is not \(F\) evaluated only on real ordinate differences.
The kernel cannot be removed using this identity.

## 4. Bound, interchange, and endpoints

The theorem proves
\[
|\mathcal R^K_{3,T}[F;\omega]|
\ll \|\phi\|_1(1+\|\omega\|_\infty+\|\omega'\|_1)
B^{-\varepsilon}\log^4(2T+2),
\]
with an effective absolute constant. To transfer the parameter range
without changing conventions, use
\[
\theta_T=\frac{\log(T/2\pi)}{\log T},\quad
\varepsilon_T=\varepsilon\theta_T,\quad
T^{-\varepsilon_T}=B^{-\varepsilon}.
\]
Here \(0<\theta_T<1\), \(X,Y\ge T^{\varepsilon_T}\), and
\(Z\le T^{(1-\varepsilon)\theta_T}\le T^{1-\varepsilon_T}\).
Apply the explicit margin-uniform bound pointwise; no unproved
varying-epsilon asymptotic is invoked.

At fixed \(T,\phi,\omega\), the integrated absolute zero-series majorant is
\[
C\|\phi\|_1B^{1-\varepsilon}\log^3(2T+2).
\]
It justifies the frequency/zero interchange and removal of independent
zero cutoffs. Complex arguments are controlled by their frequency
representation, not by real-axis Schwartz decay.
Only then take \(T\to\infty\), with the test function, support margin, and
smoothing fixed. For varying families, a zero limit requires the displayed
bound to vanish.

The condition \(T>2\pi\) is strict. Boundaries of the inner triangle
\(\Omega_\varepsilon\) are included; the axes, origin and outer line
\(\xi+\eta=1\) are excluded. Swapping \(i_2,i_3\) swaps the test arguments.
Simultaneous horizontal reflection remains a reindexing of the full
statistic, including the transformed kernel; it is not termwise invariance.

## 5. Scope and verification

This proves a vanishing interior limit for arbitrary tests in the stated
Fourier class, with the native smoothing kernel and horizontal shifts.
It does not complete the general Work Package B target. The next research
step is analysis near the frequency axes and origin, followed by any
justified extension of the support or modification of the kernel.
No GUE main term, relative asymptotic, real-ordinate-only formula, positivity,
or new horizontal constraint follows from this zero limit.

Run the exact finite checks:

~~~bash
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py' -v
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v
~~~

They verify algebra, weight joins, signed accounting, resonance bounds,
range exponents, Fourier arguments, normalization and support margins.
They are regression aids, not a numerical or analytic proof certificate.

Validation on 2026-10-02: all 41 triple checks (including nine new
retained-term/test-function checks) and all 70 pair checks passed.
Three pdflatex passes with shell escape disabled produced a seventeen-page
proof with no final-pass warnings, unresolved references, or
overfull/underfull boxes. Ledger dependency acyclicity, source labels and
documentation links are checked by the suite.

The pair RH-audit ledger hash was refreshed after verifying that the
previous ledger is an unchanged byte prefix with exactly these three
claims appended. Its existing audit metadata and claim coverage, the
pair proof, and the Work Package A reproduction archive remain unchanged.
