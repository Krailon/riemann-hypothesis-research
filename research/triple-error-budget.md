# Uniform triple estimates and named error budget

Task: proof and exposition. Assumptions: **UNCONDITIONAL**.
Initial claim: **TRIPLE-UNIFORM-001**, status **proved-draft**.
The sharper estimates and additive formula in Sections 5–6 are also
**proved-draft**, recorded as **TRIPLE-LOG-GAP-001**,
**TRIPLE-OFFDIAG-001**, and **TRIPLE-SMOOTHED-ADDITIVE-001**.
Source: [triple proof](../proofs/triple_explicit_formula.tex),
label **lem:triple-uniform**; registry: [theorem ledger](theorem-ledger.yaml).
This extends the [exact master identity](triple-master-bookkeeping.md).

## 1. Range and reusable bounds

Throughout \(T\ge3,\ X,Y\ge1,\ Z=XY\). The real nonnegative smooth weight
\(\omega\) is compactly supported in \((1,2)\), with integral one.
Use \(d\mu_T(t)=T^{-1}\omega(t/T)\,dt\), a probability measure. Put
\[
q=\log T,\quad L=\log(2T+2),\quad \ell_x=\log(2x),\qquad
W_0=\|\omega\|_1=1,\quad W_\infty=\|\omega\|_\infty,\quad W_1=\|\omega'\|_1.
\]

The constants below are effective and absolute. The inherited constants
are not given numerical values.

| Quantity | Uniform majorant | Proof input |
| --- | --- | --- |
| \(\|P_x\|_\infty\), \(\sum_n a_x(n)\) | \(b_x=C_B\sqrt{x}\ell_x\) | Elementary coefficient estimates; \(C_B=1+2/(1-2^{-1/2})^2\). |
| \(\sum_{n\ge2}a_x(n)/\log n\) | \(C_1\sqrt{x}\) | Same estimates; \(C_1=1+2/(1-2^{-1/2})\). |
| \(\|P_x\|_{L^2(\mu_T)}\) | \(m_x\), defined below | **PAIR-PRIME-MEAN-001** on \([0,2T]\), or sup norm. |
| \(\|A_x\|_{L^\infty(T,2T)}\) | \(\alpha_x=L/x\) | Exact definition. |
| \(E_{\rm arch}(x,t)\) in absolute value | \(h_{\rm arch}(x)=C_{\rm arch}/x\) | **PAIR-EF-001**. |
| \(E_{\rm DS}(x,t)\) in absolute value | \(h_{\rm DS}(x)=C_{\rm DS}/x\) | **PAIR-EF-001**. |
| \(E_{\rm pole}(x,t)\) in absolute value | \(h_{\rm pole}(x)=4\sqrt{x}/(1+T^2)\) | Same, restricted to \(T<t<2T\). |
| \(E_{\rm trivial}(x,t)\) in absolute value | \(h_{\rm trivial}(x)=12x^{-5/2}/(T+2)\) | Same, restricted to \(T<t<2T\). |

With \(C_M=\sqrt{2C_{\rm pair}}\), where
\(\int_0^V|P_x|^2dt\le C_{\rm pair}V\ell_x\) for \(1\le x\le V\),
\[
m_x=
\begin{cases}
\min\{b_x,C_M\sqrt{W_\infty\ell_x}\},&1\le x\le2T,\\
b_x,&x>2T.
\end{cases}
\]
The full budget is valid for every \(X,Y\ge1\). If \(XY\le2T\), all three
prime slots admit the sharper branch. Equality is included. This branch
boundary is not a Fourier-support condition; continuity of the majorant
across it is not required.

Set \(h_x=h_{\rm arch}(x)+h_{\rm DS}(x)+h_{\rm pole}(x)+h_{\rm trivial}(x)\)
only after retaining the four component bounds. Let
\[
\begin{split}
J_r&=\int_1^2\omega(u)\log^r(Tu+2)\,du,\qquad q^r\le J_r\le L^r,\\
D(a,b)&=\sum_{n\ge1}a_a(n)a_b(n),\qquad
0\le D(a,b)\le d_{a,b}:=C_D\sqrt{\ell_a\ell_b},\\
\Omega_{r,1}&=\|(\omega(u)\log^r(Tu+2))'\|_1
\le V_r:=W_1L^r+rW_0L^{r-1}\quad(r=1,2).
\end{split}
\]
The weighted functions are extended by zero outside \((1,2)\).
The bound for \(D(a,b)\) uses **PAIR-PRIME-DIAGONAL-001** and sequence
Cauchy–Schwarz. Prime powers are included; this notation is separate
from the zero denominators \(D_j(t)\).

## 2. Exact accounting for the eight words without H

The retained expression is
\[
M_T=\frac{q^3}{Z^2}+\frac{J_1}{Y}D(X,Z)+\frac{J_1}{X}D(Y,Z)-R_{\rm res}.
\]
It is not asserted to be an asymptotic main term. The exact full identity is
\[
\begin{split}
C_{3,T}={}&M_T+E_{\rm archcube}+E_{PPA}+E_{PAA}+E_{APA}+E_{AAP}\\
 &+E_{PAP,{\rm off}}+E_{APP,{\rm off}}+E_{PPP,{\rm off}}
 +\sum_{w:\,H\text{ occurs}}E_w .
\end{split}
\]
Here \(I_T\) conjugates its third slot, and \(R_{\rm res}\) is the
nonnegative same-prime-power resonance from **TRIPLE-MASTER-001**.

| Word | Retained contribution | Named signed error: exact definition | Absolute bound |
| --- | --- | --- | --- |
| AAA | \(q^3/Z^2\) | \(E_{\rm archcube}=(J_3-q^3)/Z^2\) | \((L^3-q^3)/Z^2\); nonnegative |
| PPA | none | \(E_{PPA}=I_T(P_X,P_Y,A_Z)\) | \(b_Xb_YV_1/(ZT\log4)\) |
| PAA | none | \(E_{PAA}=-I_T(P_X,A_Y,A_Z)\) | \(C_1\sqrt{X}V_2/(TYZ)\) |
| APA | none | \(E_{APA}=-I_T(A_X,P_Y,A_Z)\) | \(C_1\sqrt{Y}V_2/(TXZ)\) |
| AAP | none | \(E_{AAP}=-I_T(A_X,A_Y,P_Z)\) | \(C_1\sqrt{Z}V_2/(TXY)\) |
| PAP | \(J_1D(X,Z)/Y\) | \(E_{PAP,{\rm off}}=I_T(P_X,A_Y,P_Z)-J_1D(X,Z)/Y\) | \((L/Y)(m_Xm_Z+d_{X,Z})\) |
| APP | \(J_1D(Y,Z)/X\) | \(E_{APP,{\rm off}}=I_T(A_X,P_Y,P_Z)-J_1D(Y,Z)/X\) | \((L/X)(m_Ym_Z+d_{Y,Z})\) |
| PPP | \(-R_{\rm res}\) | \(E_{PPP,{\rm off}}=-I_T(P_X,P_Y,P_Z)+R_{\rm res}\) | \(U+R_{\rm res}\le U+b_Xb_Yb_Z\) |

In these bounds,
\[
U=\min\{b_Xm_Ym_Z,\ b_Ym_Xm_Z,\ b_Zm_Xm_Y\},\qquad
|I_T(P_X,P_Y,P_Z)|\le U,\quad 0\le R_{\rm res}\le b_Xb_Yb_Z.
\]
Each \(V_r\) can be replaced by the sharper \(\Omega_{r,1}\).
The exact \(J_1,D,R_{\rm res}\) terms are retained without further
asymptotic replacement, so no additional replacement errors are present.

The oscillatory estimate is
\[
\left|\int_1^2\omega(u)\log^r(Tu+2)e^{-iTu\lambda}\,du\right|
\le\frac{\Omega_{r,1}}{T|\lambda|}\quad(\lambda\ne0).
\]
For PPA, \(\lambda=\log(mn)\ge\log4\). For PAA, APA and AAP it is,
respectively, \(\log n,\log n,-\log n\).
For PAP and APP it is \(\log(m/k)\) and \(\log(n/k)\), with their
equal-index diagonals removed exactly.
The Fourier frequency is always \(T\lambda/(2\pi)\). Substitution
\(t=Tu\) cancels the original \(1/T\); differentiation cancels \(2\pi\).
Compact smoothing produces no boundary terms.

The initial two mixed-prime off-diagonal bounds and the cubic off-resonance bound
use triangle inequalities. They are uniform but do not establish
cancellation or a negligible error on a growing parameter range.
Section 5 supplies additional bounds for these same signed errors.

## 3. All nineteen remainder-containing words

The sign below is already included in the definition
\(E_w=(-1)^{\#P}I_T(w_1{}_X,w_2{}_Y,w_3{}_Z)\).
The table's bound is nonnegative. The column headed “Refinements” gives
the number of distinct ordered assignments of the four named remainders.

| Word | Sign | Absolute bound | Refinements |
| --- | --- | --- | --- |
| PPH | + | \(m_Xm_Yh_Z\) | 4 |
| PAH | - | \(m_X\alpha_Yh_Z\) | 4 |
| PHP | + | \(m_Xh_Ym_Z\) | 4 |
| PHA | - | \(m_Xh_Y\alpha_Z\) | 4 |
| PHH | - | \(m_Xh_Yh_Z\) | 16 |
| APH | - | \(\alpha_Xm_Yh_Z\) | 4 |
| AAH | + | \(\alpha_X\alpha_Yh_Z\) | 4 |
| AHP | - | \(\alpha_Xh_Ym_Z\) | 4 |
| AHA | + | \(\alpha_Xh_Y\alpha_Z\) | 4 |
| AHH | + | \(\alpha_Xh_Yh_Z\) | 16 |
| HPP | + | \(h_Xm_Ym_Z\) | 4 |
| HPA | - | \(h_Xm_Y\alpha_Z\) | 4 |
| HPH | - | \(h_Xm_Yh_Z\) | 16 |
| HAP | - | \(h_X\alpha_Ym_Z\) | 4 |
| HAA | + | \(h_X\alpha_Y\alpha_Z\) | 4 |
| HAH | + | \(h_X\alpha_Yh_Z\) | 16 |
| HHP | - | \(h_Xh_Ym_Z\) | 16 |
| HHA | + | \(h_Xh_Y\alpha_Z\) | 16 |
| HHH | + | \(h_Xh_Yh_Z\) | 64 |

For each H-slot assignment
\(\kappa:\{i:w_i=H\}\to\{{\rm arch},{\rm DS},{\rm pole},{\rm trivial}\}\),
define the stable component name \(E_{w;\kappa}\) by replacing every H
with that exact \(E_\nu(x_i,t)\). Preserve its slot, the table sign, and
conjugation in slot three. Thus, for example,
\[
E_{PHH;(2:{\rm pole},3:{\rm DS})}
=-I_T(P_X,E_{\rm pole}(Y,\cdot),E_{\rm DS}(Z,\cdot)),
\qquad
|E_{PHH;(2:{\rm pole},3:{\rm DS})}|
\le m_Xh_{\rm pole}(Y)h_{\rm DS}(Z).
\]
In every row replace each \(h_{x_i}\) by \(h_{\kappa(i)}(x_i)\) to obtain
the corresponding component bound. This names and bounds every component
without hiding its \(T,x_i\) dependence. There are
\(12\cdot4+6\cdot16+64=208\) components, and exactly \(E_w=\sum_\kappa E_{w;\kappa}\).

All H-containing rows have at most two prime slots. Their bounds follow
from sup norms for the non-prime slots and Cauchy–Schwarz for the prime
slots, with \(\|P\|_{L^1(\mu_T)}\le\|P\|_{L^2(\mu_T)}\).
Finite distributivity then gives the aggregate bounds. Do not add both
an aggregate and its components to the budget.

## 4. Dependencies, endpoints, and unresolved losses

| Part | Input and present strength |
| --- | --- |
| Exact zero/prime correspondence, signed words and resonance | **TRIPLE-MASTER-001**, retaining all horizontal coordinates and multiplicities. |
| Prime coefficient sup bounds and integration by parts | Elementary estimates; same-sign two-prime and one-prime errors gain \(1/T\). |
| Mixed-prime diagonal bound | **PAIR-PRIME-DIAGONAL-001**, including its PNT-level input. |
| Weighted prime norms | **PAIR-PRIME-MEAN-001**, including the existing unconditional mean-value and prime-counting dependencies. |
| Four remainder components | **PAIR-EF-001**, restricted to the smooth center window. |
| Mixed-prime and cubic off-diagonals | Initial triangle-inequality bounds above; Section 5 improves them using the new logarithmic-gap lemma. No prime-pair/triple conjecture is assumed. |

The endpoints \(T=3,X=1,Y=1,x=2T\) are included. Integer coefficient
splits at \(n=x\) count the endpoint once. The smooth center window does
not truncate zero ordinates, so the master identity's small-height and
multiplicity conventions persist. Simultaneous horizontal reflection
remains a reindexing of that identity. Swapping \(X,Y\) exchanges the
corresponding ordered budget rows.

Fix \(T,X,Y,\omega\), then remove prime and zero cutoffs using the master
identity's absolute majorants. The new integration-by-parts operations
act on smooth weights, never on an infinite differentiated prime series.
All rearranged coefficient sums are absolutely convergent; the
nineteen-to-208 refinement is finite. No joint asymptotic or shrinking
smoothing-width limit is invoked. Uniformity for varying weights retains
\(W_\infty,W_1\) explicitly.

There is no height-truncation, desmoothing, or support-boundary error:
those operations have not been performed. Zero-index diagonals and
prime resonances remain different decompositions. Sections 5–6 combine
the improved bounds on a growing parameter range. The resulting additive
formula supplies neither a general Fourier-support theorem nor a new
horizontal conclusion.

## 5. Sharper off-diagonal bounds

Source: **TRIPLE-LOG-GAP-001**, label **lem:triple-log-gap**, and
**TRIPLE-OFFDIAG-001**, label **lem:triple-offdiag** in the proof.
These estimates apply for every \(T\ge3,\ X,Y\ge1\), without requiring
\(XY\le2T\). Constants are absolute and effective.

| Existing signed error | Additional absolute bound |
| --- | --- |
| \(E_{PPP,{\rm off}}\) | \(O(W_1Z\ell_Z^4/T)\) |
| \(E_{PAP,{\rm off}}\) | \(O((\Omega_{1,1}/T)(X/\sqrt Y)(\ell_X\ell_Z)^{3/2})\) |
| \(E_{APP,{\rm off}}\) | \(O((\Omega_{1,1}/T)(Y/\sqrt X)(\ell_Y\ell_Z)^{3/2})\) |

Both the old and new bounds remain valid; their minimum is available.
These are new estimates of existing errors, not extra summands.
The mixed diagonals and the negative cubic resonance are unchanged.

For complex sequences on integers \(n\ge2\), let
\[
B(c)=\sum_n|c_n|,\qquad \mathcal E(c)=\sum_n n\log(2n)|c_n|^2.
\]
The new gap lemma proves the explicit inequality
\[
\sum_{m\ne n}\frac{|c_md_n|}{|\log(m/n)|}
\le \frac{B(c)B(d)}{\log2}
   +4\sqrt2\sqrt{\mathcal E(c)\mathcal E(d)}.
\]
It assumes both coefficient sums and both energies are finite. The proof
splits at ratios \(1/2,2\), uses integer gaps and harmonic sums on
comparable indices, and proves absolute convergence by monotone convergence.
Ratios exactly \(1/2,2\) belong to the comparable part; the diagonal is
excluded before division.

To use this for the cubic, combine all repeated product frequencies:
\[
c_{X,Y}(r)=\sum_{\substack{mn=r\\m,n\ge2}}a_X(m)a_Y(n),\qquad
P_XP_Y=\sum_{r\ge2}c_{X,Y}(r)r^{-it}.
\]
All ordered factorizations contribute. Tonelli gives
\(B(c_{X,Y})=B(a_X)B(a_Y)\). With \(v_x(n)=\min(n/x,x/n)\),
\[
v_X(m)v_Y(n)\le v_Z(mn),\qquad
(\Lambda*\Lambda)(r)\le\log^2r,\qquad
c_{X,Y}(r)\le r^{-1/2}v_Z(r)\log^2r.
\]
The divisor bound follows directly from \(\sum_{d\mid r}\Lambda(d)=\log r\).
Dyadic summation proves
\[
\mathcal E(a_x)\le K_3x\ell_x^3,\qquad
\mathcal E(c_{X,Y})\le K_5Z\ell_Z^5,\qquad
K_k=1+2\sum_{j\ge0}2^{-j}(j+2)^k<\infty.
\]
One integration by parts supplies \(W_1/(T|\log(r/k)|)\), or
\(\Omega_{1,1}/(T|\log(m/k)|)\) for the mixed-prime weight.
The gap lemma now controls the entire off-diagonal, including large
indices with small relative gaps. No prime-pair/triple conjecture or
additional sieve estimate is used.

The removed cubic diagonal is exactly
\(\sum_r c_{X,Y}(r)a_Z(r)=R_{\rm res}\). Frequencies use
\(T\log(r/k)/(2\pi)\); all signs and normalization are inherited unchanged.
Absolute coefficient sums justify convolution and integration; the finite
reciprocal-log majorants justify removal of off-diagonal cutoffs in any
order at fixed parameters.

## 6. Additive formula on an interior growing range

Source: **TRIPLE-SMOOTHED-ADDITIVE-001**, label
**cor:triple-smoothed-additive**. For
\[
0<\varepsilon<1/3,\qquad T\ge3,\qquad
T^\varepsilon\le X,Y,\qquad Z=XY\le T^{1-\varepsilon},
\]
the existing retained expression satisfies
\[
|C_{3,T}(X,Y)-M_T|
\le C(1+W_\infty+W_1)T^{-\varepsilon}L^4
\]
with an absolute effective \(C\), independent of epsilon and the other
parameters. For fixed epsilon and smoothing this gives \(C_{3,T}=M_T+o(1)\)
uniformly over the stated range.

| Budget contribution | Absolute bound up to an effective absolute constant |
| --- | --- |
| \(E_{\rm archcube}\) | \(T^{-4\varepsilon}L^2\) |
| \(E_{PPA}\) | \((1+W_1)T^{-1-\varepsilon}L^3\) |
| \(E_{PAA},E_{APA}\) | \((1+W_1)T^{-1-5\varepsilon/2}L^2\) |
| \(E_{AAP}\) | \((1+W_1)T^{-1-\varepsilon}L^2\) |
| \(E_{PAP,{\rm off}},E_{APP,{\rm off}}\) | \((1+W_1)T^{-\varepsilon}L^4\) |
| \(E_{PPP,{\rm off}}\) | \(W_1T^{-\varepsilon}L^4\) |
| Sum of the nineteen H-containing words | \((1+W_\infty)T^{-\varepsilon}L^2\) |

Indeed every base \(x=X,Y,Z\) lies between \(T^\varepsilon\) and
\(T^{1-\varepsilon}<2T\), while \(Z\ge T^{2\varepsilon}\). Hence
\(m_x\ll\sqrt{W_\infty L}\), \(\alpha_x\le T^{-\varepsilon}L\), and
\(h_x\ll T^{-\varepsilon}\). The pole component is bounded by
\(4T^{-(3+\varepsilon)/2}\); the trivial-zero component by
\(12T^{-1-5\varepsilon/2}\). The H-containing words split into three with
two P slots, nine with one, and seven with none, giving
\[
\sum_{w:\,H\text{ occurs}}|E_w|
\ll W_\infty T^{-\varepsilon}L
  +\sqrt{W_\infty}T^{-2\varepsilon}L^{3/2}
  +T^{-3\varepsilon}L^2.
\]
This proves the last row without double counting component refinements.
The remaining rows follow from Sections 2 and 5; the proof gives their
individual exponent calculations.

The \(X,Y,Z\) boundaries and \(T=3\) are included. The range is nonempty:
\(X=Y=T^\varepsilon\) is admissible. Epsilon is strictly between 0 and
\(1/3\); no epsilon-zero or varying-epsilon limit is claimed.
First remove convergent cutoffs at fixed parameters, then let \(T\) grow
with epsilon and smoothing fixed. For varying weights, the explicit
estimate remains valid but its displayed right side must tend to zero
to conclude \(o(1)\).

This is an additive formula, not relative error \(o(M_T)\).
The original retained expression remains exact and has not been shown
to dominate the error. Full horizontal zero coordinates and multiplicities
are retained. This parameter range by itself is not a proved Fourier-support region.

The subsequent [retained-term evaluation and test-function theorem](triple-test-functions.md)
record **TRIPLE-RETAINED-001**, **TRIPLE-INTERIOR-VANISHING-001**, and
**TRIPLE-TEST-FUNCTION-001**. They evaluate \(J_1,D\), give a decaying
proper-power bound for \(R_{\rm res}\), and prove the interior observable
tends to zero. The exact refinements \(E_D,E_J\) belong inside \(M_T\);
they are not additional errors when \(M_T\) is retained in this budget.
The resulting test-function theorem covers compact Fourier support inside
the positive triangle with the native kernel and complex zero arguments.
Analysis at the axes and origin, the general Work Package B theorem,
a GUE main term, and horizontal consequences remain open.

## 7. Regression checks

Run the standard-library exact checks with:

~~~bash
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py' -v
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v
~~~

The checks cover word/component accounting, signed diagonal extraction,
conjugation, norm-bound assignment, oscillatory scales, endpoints,
dependencies and source labels. They are verification aids, not an
analytic or numerical proof certificate.

Validation of the initial uniform-budget draft on 2026-10-01: all 22 triple checks (11 master-identity and
11 uniform-budget checks) and all 70 pair checks passed. Three
pdflatex passes with shell escape disabled compiled the expanded draft
to ten pages, with no final-pass warnings, unresolved references, or
overfull/underfull boxes.

The existing pair RH audit retains its original claim coverage.
On 2026-10-01 its ledger hash was refreshed after verifying that the previous ledger
is an unchanged byte prefix and only TRIPLE-UNIFORM-001 was appended.
This metadata review does not extend that audit to Work Package B.

Validation on 2026-10-02: all 32 triple checks (including ten new
off-diagonal/additive checks) and all 70 pair checks passed. Three
pdflatex passes with shell escape disabled compiled the expanded proof
to fourteen pages with no final-pass warnings, unresolved references,
or overfull/underfull boxes. Dependency acyclicity, source labels,
documentation links and whitespace checks passed.

The additional ledger hash refresh on 2026-10-02 records an unchanged
previous-ledger prefix followed by exactly the three new claims
TRIPLE-LOG-GAP-001, TRIPLE-OFFDIAG-001 and TRIPLE-SMOOTHED-ADDITIVE-001.
Existing audit metadata, its claim coverage, the pair proof, and the
Work Package A archive remain unchanged.
