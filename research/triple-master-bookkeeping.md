# Exact smoothed triple identity: bookkeeping

Task: proof and exposition. Assumptions: `UNCONDITIONAL`.
Claim: **TRIPLE-MASTER-001**, status **proved-draft**.
Source: [proof draft](../proofs/triple_explicit_formula.tex),
label `lem:triple-master`. This is an exact weighted identity; the Work
Package B support-restricted asymptotic is still a target.

## Observable and dependencies

For \(T\ge3\), \(X,Y\ge1\), \(Z=XY\), fix real nonnegative
\(\omega\in C_c^\infty((1,2))\) with \(\int\omega=1\). Define

\[
I_T(f,g,h)=T^{-1}\int_{\mathbb R}\omega(t/T)fg\overline h\,dt,
\qquad C_{3,T}(X,Y)=I_T(S_X,S_Y,S_Z).
\]

The full-zero sum \(S_x\) is the one in `PAIR-EF-CONVERGENCE-001`;
all nontrivial zero occurrences, both signs and all multiplicities, occur.
The center window does not truncate the zeros. Powers use the real logarithm.
The dependencies are:

| ID | Imported content |
| --- | --- |
| `PAIR-EF-CONVERGENCE-001` | Absolute and locally uniform convergence of \(S_x,P_x\). |
| `PAIR-COUNT-KERNEL-001` | Effective \(Q(t)=\sum_j(1+(t-\gamma_j)^2)^{-1}\le C_0\log(\vert t\vert+2)\). |
| `PAIR-EF-001` | Exact \(S_x=-P_x+A_x+H_x\), with four separately bounded remainders. |

Here \(A_x(t)=x^{-1}\log(|t|+2)\) and
\(H_x=E_{\rm arch}+E_{\rm DS}+E_{\rm pole}+E_{\rm trivial}\).
These are exact functions, reproduced in `eq:triple-H` of the proof.
The bounds are respectively \(C_{\rm arch}/x\), \(C_{\rm DS}/x\),
\(4\sqrt{x}/(1+t^2)\), \(12x^{-5/2}/(|t|+2)\).
No aggregate smallness assertion is attached to \(H\).

## Zero-side identity and five index patterns

Write \(\rho_j=1/2+\delta_j+i\gamma_j\),
\(D_j(t)=1+((t-\gamma_j)+i\delta_j)^2\), and

\[
K_T(j,k,\ell)=T^{-1}\int\frac{\omega(t/T)}{D_jD_k\overline{D_\ell}}\,dt,
\quad
B_{jk\ell}=8X^{\rho_j+\bar\rho_\ell-1}
              Y^{\rho_k+\bar\rho_\ell-1}K_T(j,k,\ell).
\]

Then \(C_{3,T}=\sum_{j,k,\ell}B_{jk\ell}\). In particular, the horizontal
factor is \(X^{\delta_j+\delta_\ell}Y^{\delta_k+\delta_\ell}\);
the phases are \(X^{i(\gamma_j-\gamma_\ell)}Y^{i(\gamma_k-\gamma_\ell)}\).
The factor 8 comes from the three factors 2 in \(S\).

| Partition | Disjoint index condition | Subseries | Count for \(q\) occurrences |
| --- | --- | --- | --- |
| `123` | \(j=k=\ell\) | \(\sum_jB_{jjj}\) | \(q\) |
| `12\|3` | \(j=k\ne\ell\) | \(\sum_{j\ne\ell}B_{jj\ell}\) | \(q(q-1)\) |
| `13\|2` | \(j=\ell\ne k\) | \(\sum_{j\ne k}B_{jkj}\) | \(q(q-1)\) |
| `23\|1` | \(k=\ell\ne j\) | \(\sum_{j\ne k}B_{jkk}\) | \(q(q-1)\) |
| `1\|2\|3` | pairwise distinct indices | \(\sum_{j,k,\ell\text{ distinct}}B_{jk\ell}\) | \(q(q-1)(q-2)\) |

Distinct indices can represent the same complex zero. Equal ordinates can
belong to different complex zeros. The partial diagonals have not been
collapsed into three copies of one row.

Swapping \(X,Y\) and the first two slots preserves the observable.
Simultaneously reflecting all zero occurrences by \(\rho\mapsto1-\bar\rho\)
preserves each subseries by reindexing: it negates every \(\delta\) and
conjugates every \(D\), without changing the ordinate phases. The summands
are not individually invariant. Reflecting one slot alone need not preserve
an index diagonal. No full permutation symmetry or positivity is claimed.

## All 27 ordered prime/archimedean/remainder terms

A row gives its sign times \(I_T(w_1{}_X,w_2{}_Y,w_3{}_Z)\).
The third slot is always conjugated, including its remainder components.
The sign is \((-1)^{\#P}\). The table has eight rows without \(H\) and
nineteen with \(H\).

| Word | Sign | Integrand before the height weight | Contains H |
| --- | --- | --- | --- |
| PPP | - | \(P_XP_Y\overline{P_Z}\) | no |
| PPA | + | \(P_XP_Y\overline{A_Z}\) | no |
| PPH | + | \(P_XP_Y\overline{H_Z}\) | yes |
| PAP | + | \(P_XA_Y\overline{P_Z}\) | no |
| PAA | - | \(P_XA_Y\overline{A_Z}\) | no |
| PAH | - | \(P_XA_Y\overline{H_Z}\) | yes |
| PHP | + | \(P_XH_Y\overline{P_Z}\) | yes |
| PHA | - | \(P_XH_Y\overline{A_Z}\) | yes |
| PHH | - | \(P_XH_Y\overline{H_Z}\) | yes |
| APP | + | \(A_XP_Y\overline{P_Z}\) | no |
| APA | - | \(A_XP_Y\overline{A_Z}\) | no |
| APH | - | \(A_XP_Y\overline{H_Z}\) | yes |
| AAP | - | \(A_XA_Y\overline{P_Z}\) | no |
| AAA | + | \(A_XA_Y\overline{A_Z}\) | no |
| AAH | + | \(A_XA_Y\overline{H_Z}\) | yes |
| AHP | - | \(A_XH_Y\overline{P_Z}\) | yes |
| AHA | + | \(A_XH_Y\overline{A_Z}\) | yes |
| AHH | + | \(A_XH_Y\overline{H_Z}\) | yes |
| HPP | + | \(H_XP_Y\overline{P_Z}\) | yes |
| HPA | - | \(H_XP_Y\overline{A_Z}\) | yes |
| HPH | - | \(H_XP_Y\overline{H_Z}\) | yes |
| HAP | - | \(H_XA_Y\overline{P_Z}\) | yes |
| HAA | + | \(H_XA_Y\overline{A_Z}\) | yes |
| HAH | + | \(H_XA_Y\overline{H_Z}\) | yes |
| HHP | - | \(H_XH_Y\overline{P_Z}\) | yes |
| HHA | + | \(H_XH_Y\overline{A_Z}\) | yes |
| HHH | + | \(H_XH_Y\overline{H_Z}\) | yes |

Replacing each \(H\) by its four named components gives 216 ordered
terms in the six letters \(P,A,E_{\rm arch},E_{\rm DS},E_{\rm pole},
E_{\rm trivial}\). This finite refinement is exact; each component retains
its own parameter dependence from `PAIR-EF-001`.

## Cubic prime term and Fourier units

For \(a_x(n)=\Lambda(n)n^{-1/2}\min(n/x,x/n)\),

\[
I_T(P_X,P_Y,P_Z)=\sum_{m,n,k\ge1}a_X(m)a_Y(n)a_Z(k)
  \widehat\omega\!\left(\frac{T}{2\pi}\log\frac{mn}{k}\right).
\]

This is the **unsigned** term: its coefficient in \(C_{3,T}\) is **−1**.
The project transform has the negative sign \(e^{-2\pi iu\xi}\).
Substitution \(t=Tu\) cancels \(1/T\), leaving no additional scale factor.

| Arithmetic part | Exact condition | Current treatment |
| --- | --- | --- |
| Resonance | \(mn=k\), with all three coefficients nonzero | Exactly \(m=p^a,n=p^b,k=p^{a+b}\), ordered \(a,b\ge1\); \(\widehat\omega(0)=1\). |
| Off resonance | \(mn\ne k\) | Absolutely convergent subseries; no negligible-error estimate yet. |
| Far frequencies | \(T\vert\log(mn/k)\vert\) large | Bound each transform by \(\lVert\omega^{(N)}\rVert_1/(T\vert\log(mn/k)\vert)^N\). Summed asymptotic bounds remain to be proved. |
| Near resonance | \(T\vert\log(mn/k)\vert\) bounded | Smoothness alone supplies no asymptotic suppression. |

The zero-index and arithmetic decompositions are separate. No rowwise
correspondence has been established. Compact height support supplies decay
of the transform, not a compact Fourier support or exact deletion of hard
configurations. There is no support polytope claimed at this stage.

## Convergence, endpoints, and limit order

The absolute product of the three zero sums is bounded by
\((8/3)^3XYQ(t)^3\). After multiplication by \(|\omega(t/T)|/T\),
its integral is at most
\((8/3)^3XYC_0^3\log^3(2T+2)\|\omega\|_1\).
This explicit majorant justifies Tonelli/Fubini and every index regrouping.
For primes, \(B(x)=\sum_na_x(n)<\infty\) follows from
\(a_x(n)\le x(\log n)n^{-3/2}\); the absolute integral is at most
\(\|\omega\|_1B(X)B(Y)B(XY)\).

Fix \(T,X,Y,\omega\), then remove the three independent zero cutoffs
\(|\gamma|\le U_r\), with included endpoints carrying full multiplicity.
Any order, or a joint limit, is allowed by the majorant. The same holds
for prime cutoffs. No asymptotic limit or varying smoothing width is used.
The endpoints \(X=1,Y=1,T=3\) are included. The weight vanishes near
\(T,2T\); there are no height-endpoint half weights. Every zero with
\(0<|\gamma|<3\), if present, is included. Normalization is \(1/T\),
not \(1/(T\log T)\) or mean-spacing normalization.

For varying weights, all bounds retain \(\|\omega\|_1\) and the relevant
\(\|\omega^{(N)}\|_1\). Uniformity in a shrinking smoothing width has not
been asserted. Replacing the second *input function* by 1 recovers a
smoothed pair form; setting \(Y=1\) does not, since \(S(1,t)\ne1\) in general.

## Verification and next step

Run the exact finite regression checks:

```bash
python3 -B scripts/check_triple_master.py
```

They check signs, conjugation, phases, multiplicities, reflection,
partitions, Fourier units, and prime-power resonance. Finite zero fixtures
are `SYNTHETIC_MODEL`, respecting the full symmetries. These checks are
verification aids; the written convergence argument supplies the proof.
No numerical proof certificate is used.

Validation of the initial master draft on 2026-10-01: all 11 triple checks and all 70 existing pair
checks passed. The standalone proof compiled with three `pdflatex` passes
(`-no-shell-escape`) to five pages, with no final-pass warnings, unresolved
references, or overfull/underfull boxes. Ledger dependency resolution and
acyclicity, local documentation links, and whitespace checks passed.

The next lemma, **TRIPLE-UNIFORM-001**, now supplies the
[uniform bounds and named error budget](triple-error-budget.md) for all
27 words, including all 208 named remainder refinements.
**TRIPLE-OFFDIAG-001** now improves the mixed-prime and cubic off-diagonal
bounds, and **TRIPLE-SMOOTHED-ADDITIVE-001** combines them into an additive
formula on an interior growing range. The budget records both advances.
Next: evaluate the retained terms at the intended scale and connect the
observable to a test-function correlation statement. The general
support-restricted theorem and horizontal consequences remain open.

The pair RH audit continues to cover its original Work Package A claims.
The new ledger entry is an append-only extension outside that audit's
coverage; its hash refresh records that limited review explicitly.
