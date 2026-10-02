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
It does not complete the general Work Package B target. Sections 6--7
below subsequently handle the frequency axes and origin from the positive
quadrant; Sections 8--9 extend to signed sectors. Kernel modification
remains separate.
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

## 6. Positive-quadrant boundary estimates

Task: proof and bookkeeping. Claims **TRIPLE-BOUNDARY-ESTIMATES-001**
(label **lem:triple-boundary-estimates**) and **TRIPLE-QUADRANT-LIMIT-001**
(label **thm:triple-quadrant-limit**) extend the analysis above to the
axes and origin from within the positive quadrant. Both are
**proved-draft**, with `UNCONDITIONAL` and the explicit support assumption.
The earlier interior statements retain their original domains.

Write
\[
Q=[0,\infty)^2,\quad Q_\kappa=\{(\xi,\eta)\in Q:\xi+\eta\le1-\kappa\},
\quad 0<\kappa<1.
\]
A test \(\psi\) is a restriction of a member of \(C_c^\infty(\mathbb R^2)\)
to \(Q\), with relative support in \(Q_\kappa\). Nonzero boundary
traces are allowed. Define
\[
N_1(\psi)=\|\psi\|_{\infty,Q}+\|\partial_\xi\psi\|_{\infty,Q}
+\|\partial_\eta\psi\|_{\infty,Q}.
\]
For \(T\ge2\pi e\), set \(B=T/(2\pi), b=\log B\ge1, q=\log T\),
\(L=\log(2T+2)\), and \(\mathcal W=1+W_\infty+W_1\).
Then \(b\asymp q\asymp L\) with absolute constants. Set
\(X=B^\xi,Y=B^\eta,Z=XY\), so \(1\le X,Y\le Z\le B^{1-\kappa}<T\).
The interior growing-range corollary is not used at these endpoints.

For fixed smoothing, the local profiles are
\[
q^{-3}\mathcal C_{3,T}(e^u,e^v)\longrightarrow e^{-2(u+v)},\qquad
q^{-2}\mathcal C_{3,T}(B^r,e^s)\longrightarrow r(1+s)e^{-2s}.
\]
Convergence is uniform on compact subsets of \(u,v\ge0\), respectively
\(0<r<1,s\ge0\); exchange the arguments for the other axis.
Thus the pointwise sizes are \(q^3\) at the origin and \(q^2\) on
an axis away from the origin. These differ from the integrated scale.

Define the exact remainder
\[
R_T=\mathcal C_{3,T}-q^3/Z^2-(q+\mu_\omega)G.
\]
It consists of the eight old non-\(H\) errors, nineteen signed \(H\)
words, \(E_D,E_J\), and \(-R_{\rm res}\), each counted once.
The following entries bound integrals of absolute values over
\(Q_\kappa\), before multiplying by \(\|\psi\|_{\infty,Q}\).
All implicit constants are effective and absolute.

| Source | Integrated bound |
| --- | --- |
| \(E_{\rm archcube}\) | \(O(L^2/b^2)\) |
| \(E_D\) | \(O(L/b)\) |
| \(E_J\) | \(O(T^{-1})\) |
| \(-R_{\rm res}\) | \(O(b^{-2})\) |
| \(E_{PPA}\) | \(O((1+W_1)L^3/T)\) |
| \(E_{PAA},E_{APA},E_{AAP}\), each | \(O((1+W_1)L^2/T)\) |
| \(E_{PAP,\rm off},E_{APP,\rm off},E_{PPP,\rm off}\), each | \(O((1+W_1)B^{-\kappa}L^4)\) |
| All nineteen \(H\) words | \(O((1+W_\infty)(1+T^{-3/2}L^2))\) |

The remainder words keep all four original component labels. Split
\(H=H^0+E_{\rm pole}\). For \(H^0\), the separate bounds are
\(C_{\rm arch}/x,C_{\rm DS}/x,12/(Tx)\); every trivial component
can retain its additional \(T^{-1}\). With \((p,a,h)\) denoting counts
of \(P,A,H^0\), the following table records all nineteen words.
Bounds omit a factor \(C(1+W_\infty)\).

| Counts \((p,a,h)\) | Number | Integrated bound |
| --- | --- | --- |
| \((2,0,1)\) | 3 | \(L/b\); the third-slot remainder improves to \(L/b^2\) |
| \((1,1,1)\) | 6 | \(L^{3/2}/b^2\) |
| \((0,2,1)\) | 3 | \(L^2/b^2\) |
| \((1,0,2)\) | 3 | \(L^{1/2}/b^2\) |
| \((0,1,2)\) | 3 | \(L/b^2\) |
| \((0,0,3)\) | 1 | \(b^{-2}\) |

A nonprime factor in the \(X,Y,Z\) slot supplies decay vectors
\((1,0),(0,1),(1,1)\), respectively. Two nonprime slots therefore
supply decay in both frequency coordinates. Each refined word with a
pole factor is bounded instead by
\(C(1+W_\infty)T^{-3/2}L^2\), since \(x\le Z<T\).
This accounts for all 208 refinements without overlap. Consequently
\[
\int_Q|\psi R_T|\ll\|\psi\|_{\infty,Q}\mathcal W
(1+B^{-\kappa}L^4).
\]

## 7. One-sided limit and full-zero interpretation

The new normalized functional and its limit are
\[
\mathcal B_T[\psi]=\frac1q\int_Q\psi(\xi,\eta)
 \mathcal C_{3,T}(B^\xi,B^\eta)\,d\xi\,d\eta,
\]
\[
\mathcal B[\psi]=\frac14\psi(0,0)
 +\frac34\int_0^\infty r[\psi(r,0)+\psi(0,r)]\,dr.
\]
The theorem gives the uniform, effective estimate
\[
|\mathcal B_T[\psi]-\mathcal B[\psi]|
\ll N_1(\psi)\mathcal W\{b^{-1}+B^{-\kappa}L^3\}.
\]
The origin substitution \((u,v)=b(\xi,\eta)\) gives a factor
\(q^2/b^2\) after normalization. For the first mixed term,
\[
G_1(B^\xi,B^\eta)\,d\eta
=e^{-2s}(1+s)(\xi+s/(2b))\,ds,\qquad s=b\eta.
\]
The coefficients follow from exact exponential moments:
\[
\int_0^\infty s^ke^{-2s}\,ds=k!/2^{k+1},\quad
(1/2)^2=1/4,\quad 1/2+1/4=3/4.
\]
First-moment bounds control the replacement of the test by its trace,
with error \(O(N_1(\psi)/b)\). The proof integrates the retained
expressions under explicit majorants; it does not infer integrated
limits merely from the local profiles. The mixed terms have no extra
origin atom.

| Convention | Definition or endpoint rule |
| --- | --- |
| Frequency domain | Closed positive quadrant, relative support in \(Q_\kappa\) |
| Outer margin | Fixed \(0<\kappa<1\); \(\xi+\eta=1\) excluded |
| Axis/origin weights | Full one-sided masses; no additional half weights |
| Test traces | Continuous traces of the smooth restriction to \(Q\) |
| Integration | Planar Lebesgue measure; axis terms use the displayed coordinate \(r\) |
| Extra normalization | Precisely \(1/q=1/\log T\) in addition to the existing master kernel |
| Estimate threshold | \(T\ge2\pi e\), including equality |
| Exact identity threshold | \(T>2\pi\) |

Set
\[
F_+(z_1,z_2)=\int_Q\psi(\xi,\eta)e^{2\pi i(\xi z_1+\eta z_2)}\,d\xi\,d\eta.
\]
This is entire, and its real-plane Fourier transform is the zero
extension \(\mathbf1_Q\psi\), in the sense of tempered distributions.
**It is generally not Schwartz**: nonzero boundary traces produce jumps
in that zero extension. Arbitrary reassignment of values on the
measure-zero boundary does not change \(F_+\); the limiting functional
uses the traces determined by the smooth restriction.

The exact identity is
\[
\mathcal B_T[\psi]=\frac8q\sum_{i_1,i_2,i_3\in\mathcal I}
K_T(i_2,i_3,i_1)F_+(z_{21},z_{31}).
\]
The arguments, horizontal shifts, conjugated anchor, all ordered zero
occurrences, multiplicities and all five partial-diagonal patterns are
exactly those in Section 3. There is no extra \(L_T^2\) or height factor.
At fixed parameters the integrated absolute majorant is
\(C\|\psi\|_{L^1(Q)}B^{1-\kappa}L^3\), proving Fubini and removal of
independent zero cutoffs. Only then let \(T\to\infty\) with
\(\psi,\kappa,\omega\) fixed. For varying families, require the
explicit error bound to vanish. Exchange of the two non-anchor slots
exchanges the axes; full horizontal reflection remains a reindexing,
with the kernel denominators transformed as before.

Tests meeting one axis away from the origin isolate that axis term.
Tests with both axis traces zero isolate the origin only if their origin
trace is also zero, by continuity; to separate the origin contribution
with a nonzero value there, one may instead use signed tests whose two
weighted axis integrals vanish. Interior-supported tests give zero
limit and retain the earlier stronger unnormalized estimate.

This establishes a nonzero weighted one-sided boundary limit. Sections
8--9 subsequently handle signed sectors and Schwartz tests crossing the
axes for the native weighted observable. Kernel removal and horizontal
extraction remain separate; no new horizontal constraint or completion
of Work Package B is asserted here.

Validation of the boundary extension on 2026-10-02: all 50 triple checks
(including nine new boundary checks) and all 70 pair checks passed.
Three pdflatex passes with shell escape disabled produced a 21-page proof
with no final-pass warnings, unresolved references, or overfull/underfull
boxes. Exact checks cover exponential moments, coordinate substitutions,
normalization, the nineteen words and 208 refinements, axis exchange,
and finite models isolating the origin, an axis, or zero boundary traces.
These are verification aids, not analytic or numerical proof certificates.

The pair-audit ledger hash was refreshed after verifying that the previous
ledger is an unchanged byte prefix followed by exactly these two claims.
Its original claim coverage, claim snapshot, audited pair proof and
Work Package A reproduction archive remain unchanged. The new claims are
outside that audit's scope.

## 8. Signed sectors and reciprocal reflection

Task: proof and bookkeeping. Claim **TRIPLE-SIGNED-SECTORS-001**, label
**lem:triple-signed-sectors**, is **proved-draft**, with assumptions
`UNCONDITIONAL`. Extend the full-zero series \(S(x,t)\) to all \(x>0\).
The majorant
\[
|2x^{\delta_j+i(\gamma_j-t)}/D_j(t)|
\le (8/3)\max(x,x^{-1})^{1/2}(1+(t-\gamma_j)^2)^{-1}
\]
proves absolute, locally uniform convergence. Conjugating and reindexing
by \((\delta,\gamma)\mapsto(-\delta,\gamma)\), with multiplicity, gives
\[
S(x^{-1},t)=\overline{S(x,t)}.
\]
This uses the full zero multiset, including its transformed denominators;
it does not set any horizontal displacement to zero.

Extend \(\mathcal C_{3,T}(X,Y)\) by its same smoothed product to
\(X,Y>0\), and set
\[
\widetilde{\mathcal C}_T(\xi,\eta)=\mathcal C_{3,T}(B^\xi,B^\eta),\quad
R(\xi,\eta)=(\eta,-\xi-\eta),\quad
h(\xi,\eta)=\max\{|\xi|,|\eta|,|\xi+\eta|\}.
\]
The integrand is \(S(B^\xi,t)S(B^\eta,t)S(B^{-\xi-\eta},t)\).
Its factor permutations and conjugation give
\[
\widetilde{\mathcal C}_T(R(\xi,\eta))=\widetilde{\mathcal C}_T(\xi,\eta),\quad
\widetilde{\mathcal C}_T(-\xi,-\eta)=\overline{\widetilde{\mathcal C}_T(\xi,\eta)},\quad
\widetilde{\mathcal C}_T(\eta,\xi)=\widetilde{\mathcal C}_T(\xi,\eta).
\]
No new prime estimate at bases below one is needed.

The [machine-checkable sector table](triple-signed-sectors.json) contains
the following determinant-one maps from \(Q\). Conjugation is applied
to \(\widetilde{\mathcal C}_T(u,v)\), not to the frequency coordinates.

| Map | Image \((\xi,\eta)\) | Closed cone | Conjugate observable? |
| --- | --- | --- | --- |
| \(I\) | \((u,v)\) | \(\xi,\eta\ge0\) | No |
| \(R\) | \((v,-u-v)\) | \(\xi\ge0,\xi+\eta\le0\) | No |
| \(R^2\) | \((-u-v,u)\) | \(\eta\ge0,\xi+\eta\le0\) | No |
| \(-I\) | \((-u,-v)\) | \(\xi,\eta\le0\) | Yes |
| \(-R\) | \((-v,u+v)\) | \(\xi\le0,\xi+\eta\ge0\) | Yes |
| \(-R^2\) | \((u+v,-u)\) | \(\eta\le0,\xi+\eta\ge0\) | Yes |

The interiors are disjoint and cover the plane away from
\(\xi\eta(\xi+\eta)=0\). The closed cones overlap only on these seams.
There the integrand is \(S(1,t)|S(B^r,t)|^2\), in some factor order,
and is real, so all sector descriptions agree. Each map satisfies
\(h(\pm R^k(u,v))=u+v\), and globally
\[
h(\xi,\eta)=\tfrac12(|\xi|+|\eta|+|\xi+\eta|).
\]
The symmetries concern full sums. Reflections of selected zero slots
need not preserve an individual index-diagonal subseries.

The extended master identity retains the original \(K_T\) and complex
arguments. Collecting the anchor delta before estimating gives
\[
|B^{\xi(\delta_{i_2}+\delta_{i_1})+
       \eta(\delta_{i_3}+\delta_{i_1})}|
\le B^{(|\xi|+|\eta|+|\xi+\eta|)/2}=B^h.
\]
For integrable \(\phi\) supported in \(h\le1-\kappa\), the integrated
absolute zero-series bound is therefore
\(C\|\phi\|_1B^{1-\kappa}\log^3(2T+2)\). This proves the needed
Fubini statements without discarding any horizontal factor.

## 9. Schwartz correlation on the open hexagon

Claim **TRIPLE-SIGNED-TEST-FUNCTION-001**, label
**thm:triple-signed-test-function**, is **proved-draft**, with assumptions
`UNCONDITIONAL` and `SUPPORT(compact subset of max(abs(xi),abs(eta),abs(xi+eta))<1)`.
Let \(\phi\in C_c^\infty(\mathcal H)\) be arbitrary complex-valued, where
\[
\mathcal H=\{h<1\},\qquad \mathcal H_\kappa=\{h\le1-\kappa\},\quad0<\kappa<1.
\]
Every such test has support in some \(\mathcal H_\kappa\). The outer
hexagon vertices are \((1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)\);
its entire outer boundary is excluded. Internal axes, the diagonal
\(\xi+\eta=0\), and the origin are included. A smooth bump supported
in \((-1/4,1/4)^2\), nonzero at the origin, crosses all three seams
and has \(h\le1/2\) on its support.

For \(B=T/(2\pi),q=\log T\), define
\[
\mathcal A_T[\phi]=q^{-1}\int_{\mathbb R^2}\phi(\xi,\eta)
\widetilde{\mathcal C}_T(\xi,\eta)\,d\xi\,d\eta.
\]
The theorem gives
\[
\mathcal A_T[\phi]\longrightarrow\mathcal A[\phi]
=\frac32\phi(0,0)+\frac32\int_{\mathbb R}|r|
 [\phi(r,0)+\phi(0,r)+\phi(r,-r)]\,dr.
\]
More precisely, for support in \(\mathcal H_\kappa\), \(T\ge2\pi e\),
\(b=\log B\), and \(L=\log(2T+2)\),
\[
|\mathcal A_T[\phi]-\mathcal A[\phi]|
\ll\|\phi\|_{C^1}(1+W_\infty+W_1)
\{b^{-1}+B^{-\kappa}L^3\}.
\]
The constant is effective, absolute, and independent of \(\kappa\).
Here \(\|\phi\|_{C^1}\) is the sum of the sup norms of \(\phi\)
and its two first partial derivatives.

For the proof use quadrant tests
\[
\psi_{+,k}=\phi\circ R^k,\qquad
\psi_{-,k}=\overline{\phi\circ(-R^k)},\quad k=0,1,2.
\]
Their relative supports lie in \(Q_\kappa\) and
\(N_1(\psi_{\pm,k})\le2\|\phi\|_{C^1}\). Exactly,
\[
\mathcal A_T[\phi]=\sum_{k=0}^2
\left(\mathcal B_T[\psi_{+,k}]+
      \overline{\mathcal B_T[\psi_{-,k}]}\right).
\]
The conjugation of the negative-sector test is required even though the
limiting coefficients are real. Apply the quadrant theorem to each term.
Each of six origin contributions is \(\phi(0,0)/4\). Each of the six
rays is a column of two sector matrices and receives two contributions
\(3r/4\), yielding coefficient \(3/2\) in the full-plane formula.
The planar seams have measure zero at finite \(T\); the adjacent
sectors both contribute to the limiting line measures. No additional
half weights apply. The diagonal is parameterized by \((r,-r)\),
with measure **\(dr\)**, not Euclidean arclength; no extra
\(\sqrt2\) factor appears.

Define
\[
F(z_1,z_2)=\int_{\mathbb R^2}\phi(\xi,\eta)
 e^{2\pi i(\xi z_1+\eta z_2)}\,d\xi\,d\eta.
\]
Then \(F\) is entire, Schwartz on the real plane, and \(\widehat F=\phi\)
in the project convention. For \(T>2\pi\), the exact identity is
\[
\mathcal A_T[\phi]=\frac8q\sum_{i_1,i_2,i_3\in\mathcal I}
K_T(i_2,i_3,i_1)F(z_{21},z_{31}).
\]
It includes the full zero multiset, both ordinate signs, multiplicities,
all five index patterns, conjugated anchor and the same imaginary sums
of deltas. The only extra normalization is \(1/q\); \(1/T\) remains
in the kernel and there is no mean-spacing Jacobian.

Remove independent zero cutoffs at fixed \(T,\phi,\omega\) using the
majorant in Section 8; then let \(T\to\infty\) with test, margin and
smoothing fixed. For varying families require the displayed error to
vanish. Reality, positivity and permutation symmetry of tests are not
required. Hermitian frequency symmetry may be imposed to obtain real
Schwartz tests. A test supported strictly within one sector gives zero
limit, recovering the earlier interior behavior.

This supplies smooth Fourier tests across every internal seam for the
native weighted full-zero correlation. The one-sided class in Sections
6--7 remains a useful intermediate result with different regularity.
Kernel removal, GUE identification, and horizontal extraction remain
separate tasks; this does not assert completion of Work Package B.

Validation of the signed-sector extension on 2026-10-02: all 60 triple
checks (including ten new signed-sector checks) and all 70 pair checks
passed. The 24-page PDF compiled with shell escape disabled, with no
final-pass warnings, unresolved references, or overfull/underfull boxes.
The new exact checks cover the full-zero reciprocal reflection, bases
below one, sector geometry and seams, complex-test conjugation, collected
anchor bounds, chain-rule norms, ray incidence, support fixtures and
rejection of deliberately corrupted sector records. These are finite
verification aids, not an analytic or numerical proof certificate.

The pair-audit ledger hash was refreshed after verifying that the previous
ledger is an unchanged byte prefix followed by exactly the two signed-sector
claims. Existing claim statements, audit snapshot, audited Work Package A
proof files and reproduction archive remain unchanged. The new claims are
outside the Work Package A audit's coverage.
