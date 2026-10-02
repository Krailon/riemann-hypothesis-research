# Uniform triple estimates and named error budget

Task: proof and exposition. Assumptions: **UNCONDITIONAL**.
Claim: **TRIPLE-UNIFORM-001**, status **proved-draft**.
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

The two mixed-prime off-diagonal bounds and the cubic off-resonance bound
use triangle inequalities. They are uniform but do not establish
cancellation or a negligible error on a growing parameter range.

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
| Mixed-prime and cubic off-diagonals | Uniform triangle-inequality bounds only; sharper estimates remain open. No prime-pair/triple conjecture is assumed. |

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
prime resonances remain different decompositions. The next analytic
task is to sharpen the mixed-prime and cubic off-diagonal bounds and
assess the remainder scales on a chosen growing parameter range.
The present budget supplies neither a Fourier-support theorem nor a
new horizontal conclusion.

## 5. Regression checks

Run the standard-library exact checks with:

~~~bash
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py' -v
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v
~~~

The checks cover word/component accounting, signed diagonal extraction,
conjugation, norm-bound assignment, oscillatory scales, endpoints,
dependencies and source labels. They are verification aids, not an
analytic or numerical proof certificate.

Validation on 2026-10-01: all 22 triple checks (11 master-identity and
11 uniform-budget checks) and all 70 pair checks passed. Three
pdflatex passes with shell escape disabled compiled the expanded draft
to ten pages, with no final-pass warnings, unresolved references, or
overfull/underfull boxes.

The existing pair RH audit retains its original claim coverage.
Its ledger hash was refreshed after verifying that the previous ledger
is an unchanged byte prefix and only TRIPLE-UNIFORM-001 was appended.
This metadata review does not extend that audit to Work Package B.
