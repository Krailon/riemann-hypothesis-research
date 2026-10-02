# Consolidated pair-theorem error budget

Task: exposition. Assumptions: `UNCONDITIONAL`.
Recorded proof: `PAIR-ASYMPTOTIC-001`, status `proved-draft`.
Consolidated on 2026-09-28 from the [manuscript](../proofs/pair_baseline.tex)
and [theorem ledger](theorem-ledger.yaml).
See also the [dependency graph](dependency-graph.md) and
[notation](notation.md).

## 1. Scope, scales, and accounting

Unless a wider range is stated, all bounds below are uniform for
\(T\geq3,\ 1\leq X\leq T\). Write
\[
 q=\log T>1,\qquad \ell=\log(2X),\qquad Z_*=Tq^2.
\]
All implied constants are absolute and effective on their stated ranges.
Complete numerical values of the implied constants are not supplied.
Symbols inside `source label` references are stable LaTeX labels in
the manuscript.

The proof has two exact expansions:
\[
 R=L,\qquad
 R=TX^{-2}q^2+T\log X+E_{\rm peak}+E_{\rm mean},
\]
\[
 2\pi\Phi=L+E_{\mathrm{compare},T}+E_{\mathrm{compare},X}.
\]
Sections 2–4 specify the components of these aggregates.
The final normalization is \(2\pi\Phi/(Tq)\), with
\(C_T=Tq/(2\pi)\). It is not a replacement of \(C_T\) by \(N(T)\)
or \(TL_T\). The \(q\) here is not the scale ratio \(q_T\).

Pointwise remainders feed the square expansion; their norm bounds are
not additional summands. Likewise, prime-power contributions and
Fourier majorant bounds are already included in the errors they control.
Auxiliary tails sent to zero in proving exact identities are listed
separately in §6.

## 2. Explicit-formula remainders

Source: `PAIR-EF-001`, labels `eq:budget`,
`eq:error-bounds`, `eq:arch-ds`, together with
`PAIR-EF-EXACT-001`, labels `eq:pole`, `eq:trivial`.
For \(s=1/2+it,\ X\geq1,\ t\in\mathbb R\),
\[
 \mathcal S=-\mathcal P+X^{-1}\log(|t|+2)+
 E_{\rm arch}+E_{\rm DS}+E_{\rm pole}+E_{\rm trivial}.
\]
The exact remainder functions are
\[
 \begin{aligned}
 E_{\rm arch}&=X^{-1}\left[-\frac{\chi'}{\chi}(-1/2+it)
                                      -\log(|t|+2)\right],\\
 E_{\rm DS}&=X^{-1}\frac{\zeta'}{\zeta}(3/2-it),\\
 E_{\rm pole}&=\frac{2X^{1-s}}{s(2-s)},\\
 E_{\rm trivial}&=2\sum_{m\geq1}
       \frac{X^{-2m-s}}{(2m+s-1)(2m+s+1)}.
 \end{aligned}
\]
Here \(\chi(s)\) is the functional-equation factor used in the manuscript.
These functions may be complex; no sign assertion is made.

| Remainder | Pointwise absolute bound, \(X\geq1,\ t\in\mathbb R\) | \(b_j=\lVert E_j\rVert_{L^2(0,T)}\), \(T\geq3\) | Entry into the square |
| --- | --- | --- | --- |
| \(E_{\rm arch}\) | \(C_{\rm arch}/X\) | \(O(\sqrt T/X)\) | \(E_{P,\rm arch},E_{A,\rm arch}\), and remainder square |
| \(E_{\rm DS}\) | \(C_{\rm DS}/X\) | \(O(\sqrt T/X)\) | \(E_{P,\rm DS},E_{A,\rm DS}\), and remainder square |
| \(E_{\rm pole}\) | \(4X^{1/2}/(1+t^2)\) | \(O(\sqrt X)\) | \(E_{P,\rm pole},E_{A,\rm pole}\), and remainder square |
| \(E_{\rm trivial}\) | \(12X^{-5/2}/(\lvert t\rvert+2)\) | \(O(X^{-5/2})\) | \(E_{P,\rm trivial},E_{A,\rm trivial}\), and remainder square |

The norm bounds follow by integration of the pointwise bounds, as in
`lem:rhs-mean`. All four functions are retained.

## 3. Prime-side square

For \(t\geq0\), set \(A=X^{-1}\log(t+2)\) and
\(H=\sum_jE_j\), where \(j\) ranges over the four remainders in §2.
Then \(r=-\mathcal P+A+H=\mathcal S\), and
\[
 R=\int_0^T|r|^2\,dt=L.
\]
The coefficients and diagonal are
\[
 a_X(n)=\frac{\Lambda(n)}{\sqrt n}\min(n/X,X/n),\qquad
 D(X)=\sum_{n\geq1}a_X(n)^2.
\]
Source: `eq:prime-coefficients`.

### Exact component definitions

\[
 \begin{aligned}
 E_{\rm diagonal}&=T(D(X)-\log X),\\
 E_{\rm offdiag}&=\int_0^T|\mathcal P|^2\,dt-TD(X),\\
 E_{\rm archsquare}&=\int_0^T|A|^2\,dt-TX^{-2}q^2,\\
 E_{\rm primearch}&=-2\Re\int_0^T\mathcal P\,\overline A\,dt,\\
 E_{P,j}&=-2\Re\int_0^T\mathcal P\,\overline{E_j}\,dt,\\
 E_{A,j}&=2\Re\int_0^T A\,\overline{E_j}\,dt,\\
 E_{\rm remsquare}&=\int_0^T|H|^2\,dt\geq0.
 \end{aligned}
\]
Source: `PAIR-PRIME-MEAN-001`, labels `eq:prime-mean`,
`eq:prime-diagonal-error`; `PAIR-RHS-MEAN-001`,
labels `eq:arch-square`, `eq:prime-arch-cross`, and
the displayed expansion in `lem:rhs-mean`.

Thus the exact expansion has thirteen scalar contributions:
\[
 \begin{aligned}
 R={}&TX^{-2}q^2+T\log X+
 E_{\rm diagonal}+E_{\rm offdiag}+E_{\rm archsquare}
 +E_{\rm primearch}\\
 &+\sum_j(E_{P,j}+E_{A,j})+E_{\rm remsquare}.
 \end{aligned}
\]
Each is real; only \(E_{\rm remsquare}\geq0\) is used as a sign
property in the accounting. Its bound includes all interactions among
the four remainders, so no separate \(E_j\overline{E_k}\) term is added.

### Bounds and destinations

All rows below hold for \(T\geq3,\ 1\leq X\leq T\).
Entries bound absolute values, except the explicitly nonnegative square.
“Peak” and “mean” refer to the exact grouping immediately after the table.

| Contribution | Bound before normalization | Bound after division by \(Tq\) | Aggregate |
| --- | --- | --- | --- |
| \(E_{\rm diagonal}\) | \(O(T)\) | \(O(q^{-1})\) | mean |
| \(E_{\rm offdiag}\) | \(O(\sqrt{TX\ell})\) | \(O(\sqrt{X\ell/T}/q)\) | mean |
| \(E_{\rm archsquare}\) | \(O(Tq/X^2)\) | \(O(X^{-2})\) | peak |
| \(E_{\rm primearch}\) | \(O(\log(T+2)/\sqrt X)\) | \(O(\log(T+2)/(Tq\sqrt X))\) | mean |
| \(E_{P,\rm arch}\) | \(O(T\sqrt\ell/X)\) | \(O(\sqrt\ell/(Xq))\) | mean |
| \(E_{A,\rm arch}\) | \(O(Tq/X^2)\) | \(O(X^{-2})\) | peak |
| \(E_{P,\rm DS}\) | \(O(T\sqrt\ell/X)\) | \(O(\sqrt\ell/(Xq))\) | mean |
| \(E_{A,\rm DS}\) | \(O(Tq/X^2)\) | \(O(X^{-2})\) | peak |
| \(E_{P,\rm pole}\) | \(O(\sqrt{TX\ell})\) | \(O(\sqrt{X\ell/T}/q)\) | mean |
| \(E_{A,\rm pole}\) | \(O(\sqrt{T/X}\,q)\) | \(O((TX)^{-1/2})\) | mean |
| \(E_{P,\rm trivial}\) | \(O(\sqrt{T\ell}\,X^{-5/2})\) | \(O(\sqrt{\ell/T}\,X^{-5/2}/q)\) | mean |
| \(E_{A,\rm trivial}\) | \(O(\sqrt Tq\,X^{-7/2})\) | \(O(T^{-1/2}X^{-7/2})\) | mean |
| \(E_{\rm remsquare}\geq0\) | \(O(T/X^2+X)\) | \(O(X^{-2}/q+X/(Tq))\) | mean |

The first two rows come from `lem:prime-mean`; all remaining rows
come from `lem:rhs-mean`. In particular the latter uses
\[
 |E_{P,j}|\leq2\|\mathcal P\|_2b_j,\qquad
 |E_{A,j}|\leq2\|A\|_2b_j,\qquad
 E_{\rm remsquare}\leq\left(\sum_jb_j\right)^2,
\]
where \(\|\mathcal P\|_2\ll\sqrt{T\ell}\) and
\(\|A\|_2\ll\sqrt Tq/X\).
The prime–archimedean row uses integration by parts in each frequency,
with the absolutely convergent coefficient sum, rather than a lossier
product of these two norm bounds.

Choose the aggregate names from `eq:pair-assembly` explicitly as
\[
 E_{\rm peak}:=E_{\rm archsquare}+E_{A,\rm arch}+E_{A,\rm DS},
 \qquad
 E_{\rm mean}:=\text{sum of the other ten table entries}.
\]
These are groupings of the existing exact expansion, not extra errors.
The peak bound is \(O(Tq/X^2)\).
For the mean bound use \(q>1,\ q\leq T,\ X\leq T\),
\(\ell\leq\log(2T)\ll q\), \(\sqrt\ell/X\leq1\), and
\(\log(T+2)\ll q\). The diagonal, prime/arch and prime/DS
cross terms, and remainder square are \(O(T)\).
The off-diagonal and prime/pole terms are \(O(T\sqrt q)\).
The archimedean/pole and archimedean/trivial terms are at most
\(O(\sqrt Tq)=O(T\sqrt q)\); the prime/trivial term is at most
\(O(\sqrt{Tq})\). The oscillatory prime–archimedean term is
\(O(q)\). Hence \(E_{\rm mean}=O(T\sqrt q)\), uniformly including
\(X=1,T\). These are the two error scales in `eq:rhs-mean`.

### Prime powers and Fourier majorants are already included

| Included component | Existing bound and range | Where it is counted |
| --- | --- | --- |
| Proper-power diagonal \(D_{\rm pp}=\sum_{n=p^k,\ k\geq2}a_X(n)^2\geq0\) | \(O(X^{-1/2}\ell^3)=O(1)\), \(X\geq1\) | \(TD_{\rm pp}\) is inside \(E_{\rm diagonal}\), label `eq:primepowers-diagonal` |
| Pairs with at least one proper prime power | \(O(V\sqrt U\log^3(2U))=O(UV)\), \(U\geq2,V\geq1\) | Included in `eq:prime-pair-average`, then in \(Q(X,\delta)\), then the bound on \(E_{\rm offdiag}\) |
| Fourier majorant/minorant diagonal allowance | \(O(\delta^{-1}D(X))\) | Part of the bound on \(E_{\rm offdiag}\), not a second \(E_{\rm diagonal}\) |
| Nearby-frequency allowance | \(O(TQ(X,\delta))\), \(Q(X,\delta)\ll\delta X\) | The other part of the bound on \(E_{\rm offdiag}\) |

The prime-only weighted diagonal is
\(\log X+1-(4X^2)^{-1}+O(1)\); adding proper powers yields
\(D(X)=\log X+O(1)\). The bounded deterministic correction and the
PNT remainder are already inside \(E_{\rm diagonal}\).
Source: `PAIR-PRIME-DIAGONAL-001`, `lem:prime-diagonal`.

The proper-power pair count is a nonnegative upper bound that may
overcount pairs with two proper powers. It is not a disjoint extra
summand in the exact square. For \(0\leq V<1\) the integer-pair sum
is empty. Source: `PAIR-PRIME-COUNT-001`, `lem:prime-count`.

The Fourier allowances apply with
\[
 \mu_n=-\frac{\log n}{2\pi},\qquad
 \delta=\frac12\sqrt{\frac{\ell}{TX}},\qquad
 \frac1{2T}\leq\delta\leq\frac12.
\]
The nearby condition is strictly \(0<|\log(m/n)|<2\pi\delta\).
The two allowances give
\(\delta^{-1}D+TQ\ll\delta^{-1}\ell+T\delta X
\ll\sqrt{TX\ell}\). They are bounds from a sandwich argument, not
separately defined signed residuals.
Sources: `eq:local-meanvalue`, `eq:prime-close-pairs`,
`eq:prime-bandwidth`. Despite its name, \(E_{\rm offdiag}\)
includes the diagonal allowance of the Fourier majorants.

## 4. Zero-side comparison and signs

Use \(\mathcal U_X,\mathcal U_{X,Z},\mathcal V_{X,T}\) from
`eq:trunc-definitions` and `eq:norm-vector`.
The first sum uses every nontrivial zero occurrence, the second
retains \(|\gamma|\leq Z\), and the third retains \(0<\gamma\leq T\).
All cutoffs have full endpoint weight and multiplicity.
For \(X\geq1,\ T\geq3,\ Z\geq2T\),
\[
 \begin{aligned}
 E_{\rm trunc}&=4\int_0^T
       (|\mathcal U_X|^2-|\mathcal U_{X,Z}|^2)\,dt,\\
 E_{\rm height}&=4\int_0^T
       (|\mathcal U_{X,Z}|^2-|\mathcal V_{X,T}|^2)\,dt,\\
 E_{\rm extension}&=-4\int_{\mathbb R\setminus[0,T]}
                          |\mathcal V_{X,T}|^2\,dt\leq0,\\
 L-2\pi\Phi&=E_{\rm trunc}+E_{\rm height}+E_{\rm extension}.
 \end{aligned}
\]
Source: `PAIR-TRUNC-001`, labels `eq:trunc-decomposition`,
`eq:error-trunc-definition`, `eq:error-height-definition`,
`eq:error-extension-definition`.

Put \(B(Z)=\max(\{0\}\cup\{\beta-1/2:|\gamma|\leq Z\})\).
No sign of \(E_{\rm trunc}\) or \(E_{\rm height}\) is used.

| Error | Absolute bound for \(Z\geq2T\) | Bound at \(Z_*\), \(T\geq5,\ 1\leq X\leq T\) | Normalized comparison contribution |
| --- | --- | --- | --- |
| \(E_{\rm trunc}\) | \(O(XT[\log(T+2)\log Z/Z+\log^2Z/Z^2])=O(XT\log^2Z/Z)\) | \(O(X)\) | \(-E_{\rm trunc}/(Tq)=O(X/(Tq))\) |
| \(E_{\rm height}\) | \(O(X^{2B(Z)}q^3)\) | \(O(T)\) | \(-E_{\rm height}/(Tq)=O(q^{-1})\) |
| \(E_{\rm extension}\leq0\) | \(O(X^{2B(Z)}q^2)\) | \(O(T)\) | \(-E_{\rm extension}/(Tq)\geq0\), of size \(O(q^{-1})\) |

Source labels: `eq:error-trunc-bound`,
`eq:error-height-bound`, `eq:error-extension-bound`.
The height bounds at \(Z_*\) use `PAIR-ENVELOPE-001` and
`PAIR-COMPARE-001`:
\[
 2B(Z_*)\leq1-2\nu_{\rm KV}(Z_*),\qquad
 X^{1-2\nu_{\rm KV}(Z_*)}q^3\leq C_*T,\quad C_*=18!\,84^{18}.
\]
See `eq:finite-height-envelope` and `eq:compare-absorption`.
The factor \(C_*\) is an auxiliary absorption constant; it is not the
complete comparison constant. The \(O(X)\) row uses
\(\log Z_*\leq3q\). The extension row uses \(q^2\leq q^3\).

For \(T\geq5\), fix the comparison aggregates as
\[
 E_{\mathrm{compare},X}=-E_{\rm trunc},\qquad
 E_{\mathrm{compare},T}=-E_{\rm height}-E_{\rm extension}.
\]
This explicitly reverses the signs in \(L-2\pi\Phi\).
The combined \(E_{\mathrm{compare},T}\) has no asserted sign.

**Bounded heights \(3\leq T<5\).** The choice \(Z_*=Tq^2\) need
not satisfy \(Z_*\geq2T\), so the three specialized rows above are
not applied there. The proof instead bounds \(L\) and \(|\Phi|\)
directly by \(O(X)\), using the global kernel bound and the effective
finite count \(N(5)\). Define
\[
 E_{\mathrm{compare},X}=2\pi\Phi-L=O(X),\qquad
 E_{\mathrm{compare},T}=0
\]
on this range. No first-zero numerical information is used.
Source: the bounded-height argument in `lem:pair-trunc`,
retained in `lem:pair-compare`.

## 5. Final absorption and endpoints

Sections 3–4 give exactly
\[
 2\pi\Phi=TX^{-2}q^2+T\log X+
 E_{\rm peak}+E_{\rm mean}
 +E_{\mathrm{compare},T}+E_{\mathrm{compare},X}.
\]
Source: `eq:pair-assembly`.

| Aggregate | Uniform bound | Divided by \(Tq\) | Final destination |
| --- | --- | --- | --- |
| \(E_{\rm peak}\) | \(O(Tq/X^2)\) | \(O(X^{-2})\) | \(O(T^{-2\lvert\alpha\rvert})\) |
| \(E_{\rm mean}\) | \(O(T\sqrt q)\) | \(O(q^{-1/2})\) | \(O((\log T)^{-1/2})\) |
| \(E_{\mathrm{compare},T}\) | \(O(T)\) | \(O(q^{-1})\) | \(O((\log T)^{-1/2})\) |
| \(E_{\mathrm{compare},X}\) | \(O(X)\) | \(O(X/(Tq))\) | \(O((\log T)^{-1/2})\) |

Use \(X/(Tq)\leq q^{-1}\leq q^{-1/2}\), and substitute
\(X=T^\alpha\) only for \(0\leq\alpha\leq1\).
For negative \(\alpha\), `PAIR-POSITIVITY-001` supplies
\(\mathcal F_T(\alpha)=\mathcal F_T(|\alpha|)\);
no prime-side estimate is applied at \(X<1\).
This recovers `eq:pair-normalization` and
`eq:pair-asymptotic-bound`:
\[
 \left|\mathcal F_T(\alpha)-T^{-2|\alpha|}\log T-|\alpha|\right|
 \leq C_1T^{-2|\alpha|}+C_2(\log T)^{-1/2}.
\]

| Endpoint or convention | Treatment |
| --- | --- |
| \(T=3\) | Direct bounded-height comparison and uniform prime-side estimate |
| \(T=5\) | \(Z_*\geq2T\), so the three comparison components apply |
| \(X=1\), \(\alpha=0\) | All prime-side bounds hold; retain \(O(X^{-2})=O(1)\), giving \(\mathcal F_T(0)=\log T+O(1)\) |
| \(X=T\), \(\alpha=1\) | Mean-value bandwidth and comparison bounds include the endpoint |
| \(\alpha=-1\) | Exact evenness reduces to \(\alpha=1\) |
| \(X=p^k\) | Continuous coefficient weight; integer term counted once, no added endpoint correction |
| \(\gamma=T,\ \gamma=\pm Z\) | Full weight with multiplicity; all ordered pairs retained |

At \(\alpha=\pm1\), \(T^{-2}\log T+O(T^{-2})\) is absorbed into
\(O(q^{-1/2})\): for \(q\geq1\),
\(e^{2q}\geq2q^2\geq q^{3/2}\).
At zero the separate \(O(1)\) peak error cannot be dropped.
The bounds allow \(\alpha=\alpha(T)\in[-1,1]\) and introduce no
additional interchange of limits or extension of the frequency range.

## 6. Vanishing auxiliary tails and order of limits

These terms justify exact identities and do not survive as additional
errors in §5. In particular the contour proof's `E_height`
(`eq:horizontal-error`) is a different quantity from the
height-removal error in §4. Call the former “contour-height tail”
in this budget; the manuscript notation is unchanged.

| Auxiliary term | Bound or majorant | Limit order and source |
| --- | --- | --- |
| Full-zero series tail beyond \(U\) | \(O(X^{1/2}\log U/U)\), \(U\geq2(\lvert t\rvert+2)\) | \(U\to\infty\) at fixed \(X,t\); locally uniform for bounded \(X,t\). `eq:zero-tail` |
| Mellin-kernel horizontal and vertical integrals | Horizontal \(O_{y,R}(V^{-2})\); vertical \(O(y^{-R}/R)\) for \(y>1\), \(O(y^R/R)\) for \(y<1\), \(O(1/R)\) at \(y=1\) | First \(V\to\infty\) with \(y,R\) fixed, then \(R\to\infty\). `lem:ef-mellin` |
| Contour-height tail | \(O_{X,t,M}(\log^2U_j/U_j^2)\) | \(U_j\to\infty\) at fixed \(X>1,t,M\); no uniformity for unbounded \(X,t\) claimed. `eq:horizontal-error` |
| Left contour, \(a=2M+1\) | \(O(X^{-a-1/2}\log(a+\lvert t\rvert+2)/a)\) | After the height limit, \(M\to\infty\) at fixed \(X,t\), then \(X\downarrow1\). `eq:left-error` |
| Trivial-zero residue tail | Summable majorant \(2/m^2\) for all \(X\geq1,t\in\mathbb R\) | Residue limit justified absolutely; the full \(E_{\rm trivial}\) remains in §2. `eq:trivial-majorant` |
| Rational-integral arc and contour-shift joining segments | \(16\pi/R^3\) and \(16/R^4\), respectively, for \(R\geq4(\lvert a\rvert+1)\) | \(R\to\infty\) with the pair fixed; \(a\) is the complex pair parameter here, not the left-contour parameter above. `lem:norm-integral`, `eq:norm-shift` |
| Finite-zero squared-norm tail | \((512/27)M_X^2N(T)^2/R^3\), \(R\geq2(T+1)\), \(M_X=\max(X^{1/2},X^{-1/2})\) | \(R\to\infty\) at fixed \(X,T\); distinct from the extension error over \(\mathbb R\setminus[0,T]\). `eq:norm-tail` |
| Prime-series tail beyond \(N\) | \(O(X(\log N+1)/\sqrt N)\), \(N\geq\max(2,X)\), uniformly in \(t\) | \(N\to\infty\) at fixed \(X,T\) before the uniform mean-square estimate is applied. `lem:prime-mean` |
| Weighted prime-diagonal improper-integral tails | \(E_p(u)=O(u)\), boundary weight \(w_X(u)E_p(u)=O(X^2/u^2)\) for \(u>X\); integrable derivative and proper-power dyadic majorants | Upper endpoint tends to infinity at fixed \(X\). `lem:prime-diagonal` |

The explicit formula first fixes \(X>1,t,M\), sends \(U_j\to\infty\),
then \(M\to\infty\), and finally extends to \(X=1\) by dominated
convergence. The prime sums use absolute majorants at fixed \(X,T\).
The chosen zero cutoff \(Z_*\) in §4 is retained at finite \(T\);
its errors are estimated, not sent to zero. These distinctions prevent
auxiliary convergence arguments from creating missing final error terms.

## 7. Provenance and validation boundary

This document groups already proved-draft identities and estimates;
it introduces no new theorem, analytic input, or status upgrade.
The pointwise remainder and prime-side estimates use the ledger's
unconditional analytic, PNT, and sieve inputs. The zero-side comparison
inherits the published computer-assisted inputs through
`PAIR-ENVELOPE-001`. No certificate replay or independent
mathematical review is claimed; see the [dependency graph](dependency-graph.md).

Validation on 2026-09-28 checked 11 referenced claim IDs and 44 source
labels against the ledger and manuscript, as well as local links and
all seven table layouts. Exact exponent bookkeeping checked the
normalization of all thirteen components (including both terms in the
remainder-square bound), and the table partition has three peak and
ten mean components. The exact expansions, comparison signs, uniform
absorption inequalities and limit orders were checked against the
existing proofs. These are exposition and algebra checks, not an
independent mathematical review or a numerical certificate.
The named residuals are distinguished from internal upper bounds and
vanishing tails. The [machine-checkable convention/support table](pair-conventions.json)
and [exact checker](../scripts/check_pair_conventions.py) now cover the
scale translations, frequency ranges and auxiliary bandwidth conventions.
The remaining Work Package A tasks include the line-by-line
RH-contamination audit, clean-checkout reproduction harness, and
outstanding source and independent reviews.

The budget consolidation itself changed only documentation; no new
numerical tests or PDF rebuild were needed for that step. The theorem
ledger and manuscript remain unchanged.
