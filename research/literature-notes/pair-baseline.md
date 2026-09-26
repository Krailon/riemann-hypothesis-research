# Unconditional pair baseline: observable and normalization

Task: exposition and source verification. Assumptions: `UNCONDITIONAL`;
the explicitly marked RH specialization is a check under `RH`.
Ledger: `PAIR-BGSTB-001` (imported result), `PAIR-TRANSLATION-001`
(local algebra, `proved-draft`). Conventions: [notation](../notation.md).

Source: Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh,
*An unconditional Montgomery theorem for pair correlation of zeros of the
Riemann zeta-function*, Acta Arithmetica **214** (2024), 357–376,
[DOI](https://doi.org/10.4064/aa230612-20-3), bibliography key `BGSTB2024`.
The [publisher record](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/online/115529/an-unconditional-montgomery-theorem-for-pair-correlation-of-zeros-of-the-riemann-zeta-function)
confirms publication. The mathematical text consulted is the
[arXiv v1 PDF](https://arxiv.org/pdf/2306.04799v1), a **PREPRINT version of
the published work**; all source labels below refer to that version.
Access checked 2026-09-25. Comparison with the final journal text and the
project's proof audit are pending.

## 1. Imported theorem — PAIR-BGSTB-001

For \(T\geq3\), \(X>0\), and real \(\alpha\), define
\[
 w(z)=\frac4{4-z^2},\qquad
 \Phi(X,T)=\sum_{j,k\in I_T}X^{\rho_j-\rho_k}w(\rho_j-\rho_k),
 \qquad \mathcal F_T(\alpha)=C_T^{-1}\Phi(T^\alpha,T).
\]
Here \(X^z=\exp(z\log X)\), \(C_T=T\log T/(2\pi)\), and the sum
contains **all ordered pairs of zero occurrences** in \(0<\gamma\leq T\).
The height cutoff is sharp; the rational difference weight does not smooth it.
These are the source's (1.2)–(1.3), with its \(x,F\) renamed.

Theorem 1, equation (1.4), states that \(\mathcal F_T\) is real, even,
and nonnegative on \(\mathbb R\), and that
\[
 \mathcal F_T(\alpha)
 =T^{-2\alpha}\bigl(\log T+O(1)\bigr)
   +\alpha+O\bigl((\log T)^{-1/2}\bigr),
 \qquad 0\leq\alpha\leq1,
\]
uniformly as \(T\to\infty\), including both endpoints. Thus the two
reported error bounds are \(O(T^{-2\alpha})\) and
\(O((\log T)^{-1/2})\). Evenness gives the same statement with
\(\alpha\) replaced by \(|\alpha|\) on \([-1,1]\).
There is one limit, \(T\to\infty\); \(\alpha\) may vary within this
uniform range. Explicit constants and their effectivity remain unaudited.

This imports the full-zero observable. It supplies neither a purely vertical
unweighted correlation theorem nor a critical-line proportion by itself.
The source's Theorems 2–3 impose additional assumptions and are not imported.

## 2. Horizontal dependence and diagonals — PAIR-TRANSLATION-001

Write \(b=\beta_j-\beta_k\), \(d=\gamma_j-\gamma_k\). Each summand is
\[
 \frac{4\exp\{\alpha(x_{\rho_j}-x_{\rho_k})+i\alpha d\log T\}}
 {4-b^2+d^2-2ibd}.
\]
This follows by expanding \((b+id)^2\); \(|b|<1\) ensures the denominator
does not vanish. Both factors retain horizontal information. A single
summand need not be real or nonnegative; positivity concerns the whole sum.

In the **unnormalized** sum, the index diagonal contributes \(N(T)\).
The equal-complex-zero diagonal contributes
\(\sum_{z\in\mathcal Z_T}m(z)^2\), since each such pair has weight one.
Consequently, excluding equal indices leaves
\(\sum_z m(z)(m(z)-1)\) equal-zero pairs. Equal ordinates can also belong
to different complex zeros: their summand is \(4T^{\alpha b}/(4-b^2)\).
Divide these contributions by \(C_T\) for \(\mathcal F_T\).

Reflection of the second zero, \(\rho_k\mapsto1-\bar\rho_k\), permutes
\(I_T\) with multiplicity, so the same full sum can be written using
\(\rho_j+\bar\rho_k-1=\delta_j+\delta_k+i d\) in place of
\(\rho_j-\rho_k\) (source (2.1)). This is a reindexing of the sum;
it does not identify individual summands or preserve the original diagonal
subsets. Reflecting both zeros sends \(b+id\) to \(-b+id=-\overline{b+id}\);
combining this with exchange of indices checks the reality symmetry.

**RH specialization check (`RH`).** Setting \(b=0\) gives
\[
 \Phi(X,T)=\sum_{j,k\in I_T}
 X^{i(\gamma_j-\gamma_k)}\frac4{4+(\gamma_j-\gamma_k)^2},
\]
exactly source (1.1), retaining multiplicity. This substitution is used only
for this check.

## 3. Exact Fourier and scale translation — PAIR-TRANSLATION-001

Take \(T>2\pi\), \(A_T=\log T/(2\pi)\), and
\(q_T=A_T/L_T=\log T/\log(T/2\pi)\). With
\(u=u_{jk}=L_T(\gamma_k-\gamma_j)\), the translation is:

| Source quantity | Project expression, exact at finite \(T\) |
| --- | --- |
| Vertical phase \(T^{i\alpha(\gamma_j-\gamma_k)}\) | \(e^{-2\pi i\xi u}\), \(\xi=q_T\alpha\) |
| Horizontal phase/amplitude | \(e^{\alpha(x_{\rho_j}-x_{\rho_k})}=e^{(\xi/q_T)(x_{\rho_j}-x_{\rho_k})}\) |
| Source transform argument \(iA_T(\rho_j-\rho_k)\) | \(q_Tu+i(x_{\rho_j}-x_{\rho_k})/(2\pi)\) |
| Normalization \(C_T\) | \(q_TTL_T\), not exactly \(N(T)\) |
| \(\mathcal G_T(\xi):=(TL_T)^{-1}\Phi((T/2\pi)^\xi,T)\) | \(q_T\mathcal F_T(\xi/q_T)\) |
| Proven frequency range \(\lvert\alpha\rvert\leq1\) | \(\lvert\xi\rvert\leq q_T\); \(d\alpha=d\xi/q_T\) |

Indeed \(\log T=2\pi q_TL_T\) and
\(\log(T/2\pi)=\log T-\log(2\pi)\) prove every scale identity.
The source's transform in (3.1) has the project's negative exponential sign.
For a compactly supported smooth \(g\), its complex argument is justified by
\[
 \widehat g\bigl(iA_T(\rho_j-\rho_k)\bigr)
 =\int_{\mathbb R}g(\alpha)T^{\alpha(\rho_j-\rho_k)}\,d\alpha.
\]
The exponent identity is exact; compact support supplies absolute convergence
and locally uniform bounds for complex arguments. At fixed \(T\) the zero sum
is finite, so exchanging it with this integral is legitimate. This verifies
the translation behind (3.2); mere \(g\in L^1(\mathbb R)\), as written in
§3 of v1, would not ensure the claimed entire extension.

Support inside \([-1,1]\) in \(\alpha\) maps to \([-q_T,q_T]\) in
\(\xi\). This records the theorem's actual closed frequency interval; it
asserts no boundary extension for a later correlation theorem. Keep \(q_T\)
exact: although it tends to one, changing normalization at the height
\(\log T\) peak can produce an \(O(1)\) difference.

## 4. Inputs to reconstruct next

The following source map records the remaining reconstruction work.
Lemmas 1–4 now have local `proved-draft` reconstructions; Lemma 2 retains
Riemann–von Mangoldt as an explicitly imported input. Independent review
remains pending. Source IDs and local claim IDs are linked in the ledger.

| ID | Source locator | Role and outstanding check |
| --- | --- | --- |
| `BGSTB-EF` | Lemma 1, (2.2)–(2.3) | Reconstructed as `PAIR-EF-001`; see the [proof and endpoint audit](pair-lemma1-audit.md). Independent review and journal comparison pending. |
| `BGSTB-COUNT` | Lemma 2, (2.4)–(2.5) | Inclusive and local counts reconstructed as `PAIR-COUNT-001`; kernel bounds in `PAIR-COUNT-KERNEL-001`. See the [counting and truncation audit](pair-lemma4-audit.md). |
| `BGSTB-NORM` | Lemma 3, (2.6)–(2.8) | Reconstructed as `PAIR-NORM-001`, with integral and positivity claims; see the [contour and multiplicity audit](pair-lemma3-audit.md). Independent review and journal comparison pending. |
| `BGSTB-TRUNC` | Lemma 4, (2.13)–(2.16) | Reconstructed as `PAIR-TRUNC-001` with three named errors and a separate small-height argument; see the [audit](pair-lemma4-audit.md). Independent review and journal comparison pending. |
| `BGSTB-ZFR` | Theorem 1 proof, before (2.18) | Published KV and low-height inputs give the finite-height envelope `PAIR-ENVELOPE-001`; see the [audit](korobov-vinogradov-audit.md). The uniform \(O(T)+O(X)\) application for \(1\leq X\leq T\) remains pending. |
| `BGSTB-MEAN` | (2.17)–(2.19) and following remark | Reconstruct the prime-side mean square, including prime powers and cross terms; verify the cited Goldston–Montgomery Lemma 6 refinement and endpoint \(X=T\). |

The last row is an unresolved citation chain, not permission to use an
RH-dependent pair theorem. For the prime-side theorem assembly use
\(1\leq X\leq T\); v1's printed
\(0\leq X\leq T\) before (2.19) cannot include \(X=0\), where its formula
is undefined. The full dependency graph, named error budget, and RH
contamination audit remain Work Package A tasks.

**Completed local proof tasks:** Lemma 1 now has an exact contour identity,
absolute/local uniform convergence, prime-power and \(X=1\) conventions,
and separately bounded remainders; see [the reconstruction](../../proofs/pair_baseline.tex).
Lemma 3 now has a squared-norm proof, an explicit integral tail bound,
the off-line contour shift including coincident poles, and a
multiplicity-preserving reflection argument. Its corollary proves reality,
nonnegativity and evenness without the asymptotic theorem.
Lemma 2's inclusive/local counting consequences and Lemma 4's height
truncation are now reconstructed. The latter applies for all \(X\geq1,T\geq3\),
with `E_trunc`, `E_height` and `E_extension` bounded separately. Its
horizontal envelope is defined from the finite zero set and carries no
unproved quantitative zero-free-region assumption.
**Completed source task:** a published quantitative Korobov–Vinogradov
theorem is recorded as `ZETA-KV-001`, with explicit threshold, closed
boundary and external computational provenance. Its proof has not been
independently reconstructed or its computations replayed.
**Completed envelope proof draft:** `PAIR-ENVELOPE-001` derives
\(B(Z)<1/2-\nu_{\rm KV}(Z)\) for every \(Z\geq3\), including the
low-ordinate range through the published input `ZETA-LOW-001`.
It checks monotonicity, both signs, endpoints, multiplicity, and the empty
zero set. External computational provenance is retained in the ledger.
**Next bounded proof task:** derive the uniform \(O(T)+O(X)\)
comparison of \(L(X,T)\) and \(2\pi\Phi(X,T)\)
for \(1\leq X\leq T\). The prime-side mean square follows afterward.
The pair-correlation asymptotic itself remains an imported theorem.
