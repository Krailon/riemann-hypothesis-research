# Unconditional pair baseline: observable and normalization

Task: exposition and source verification. Assumptions: `UNCONDITIONAL`;
the explicitly marked RH specialization is a check under `RH`.
Ledger: `PAIR-BGSTB-001` (imported result), `PAIR-TRANSLATION-001`
(local algebra), and `PAIR-ASYMPTOTIC-001` (local theorem);
both local claims have status `proved-draft`.
Conventions: [notation](../notation.md).

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

## 4. Reconstructed inputs and remaining audits

The following source map records the reconstructed inputs and outstanding audits.
Lemmas 1–4 now have local `proved-draft` reconstructions; Lemma 2 retains
Riemann–von Mangoldt as an explicitly imported input. Independent review
remains pending. Source IDs and local claim IDs are linked in the ledger.

| ID | Source locator | Role and outstanding check |
| --- | --- | --- |
| `BGSTB-EF` | Lemma 1, (2.2)–(2.3) | Reconstructed as `PAIR-EF-001`; see the [proof and endpoint audit](pair-lemma1-audit.md). Independent review and journal comparison pending. |
| `BGSTB-COUNT` | Lemma 2, (2.4)–(2.5) | Inclusive and local counts reconstructed as `PAIR-COUNT-001`; kernel bounds in `PAIR-COUNT-KERNEL-001`. See the [counting and truncation audit](pair-lemma4-audit.md). |
| `BGSTB-NORM` | Lemma 3, (2.6)–(2.8) | Reconstructed as `PAIR-NORM-001`, with integral and positivity claims; see the [contour and multiplicity audit](pair-lemma3-audit.md). Independent review and journal comparison pending. |
| `BGSTB-TRUNC` | Lemma 4, (2.13)–(2.16) | Reconstructed as `PAIR-TRUNC-001` with three named errors and a separate small-height argument; see the [audit](pair-lemma4-audit.md). Independent review and journal comparison pending. |
| `BGSTB-ZFR` | Theorem 1 proof, (2.18) | Reconstructed as `PAIR-COMPARE-001`, using the finite-height envelope `PAIR-ENVELOPE-001` and published KV/low-height inputs; see the [audit](korobov-vinogradov-audit.md). Independent review and journal comparison pending. |
| `BGSTB-MEAN` | (2.17)–(2.19) and following remark | Reconstructed as `PAIR-RHS-MEAN-001`, with a local Fourier mean-value proof, published PNT/sieve inputs, prime powers, cross terms and \(X=T\) covered; see the [audit](pair-prime-mean-audit.md). Independent review and journal comparison pending. |

The cited Goldston–Montgomery mean-value estimate is proved locally in
`PAIR-MEANVALUE-001`; its original full text was inaccessible, and it
is not imported as an unchecked dependency. The theorem assembly uses
\(1\leq X\leq T\); v1's printed
\(0\leq X\leq T\) before (2.19) cannot include \(X=0\), where its formula
is undefined. The [dependency graph](../dependency-graph.md) now maps
every currently recorded dependency of the local normalized theorem,
including imported sources and computational provenance. Upstream
foundational reconstruction, the consolidated error budget, and the
RH-contamination audit remain Work Package A tasks.

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
**Completed uniform comparison draft:** `PAIR-COMPARE-001` proves
\(L(X,T)=2\pi\Phi(X,T)+O(T)+O(X)\), uniformly for \(T\geq3\) and
\(1\leq X\leq T\), with effective constants and all endpoints covered.
It keeps truncation separate from the height and extension errors and
inherits the recorded external computational provenance.
**Completed prime-side draft:** `PAIR-RHS-MEAN-001` proves
\[
 R(X,T)=TX^{-2}\log^2T+T\log X+
 O(TX^{-2}\log T)+O(T\sqrt{\log T})
\]
uniformly for \(T\geq3,1\leq X\leq T\), with \(R=L\) by the
existing explicit formula. Its local Fourier argument and published
PNT/sieve inputs retain proper prime powers and named cross-term errors.
This part uses no numerical proof input.
**Completed normalized theorem draft:** `PAIR-ASYMPTOTIC-001`
assembles these estimates, as detailed below.
**Completed dependency map:** the [graph](../dependency-graph.md) covers
26 claims, four source pointers, and all 39 recorded dependency edges.
It distinguishes proof inputs from provenance and comparison links;
upstream foundational completeness is not claimed.
**Remaining Work Package A work:** complete the
machine-checkable convention/support table, consolidated error budget,
RH-contamination audit, and clean-checkout reproduction harness.
Independent review and final journal-text comparison remain pending.

## 5. Local normalized theorem — PAIR-ASYMPTOTIC-001

Task: proof. Assumptions: `UNCONDITIONAL`. Status: `proved-draft`.
The [manuscript](../../proofs/pair_baseline.tex), label
`thm:pair-asymptotic`, proves that there are absolute effective
\(C_1,C_2>0\) such that, for every \(T\geq3\) and \(|\alpha|\leq1\),
\[
 \left|\mathcal F_T(\alpha)-T^{-2|\alpha|}\log T-|\alpha|\right|
 \leq C_1T^{-2|\alpha|}+C_2(\log T)^{-1/2}.
\]
The observable and all diagonal/multiplicity conventions are those in §1.
The normalization remains \(C_T=T\log T/(2\pi)\).
This is a local reconstruction of the imported theorem; its proof depends
on `PAIR-COMPARE-001`, `PAIR-RHS-MEAN-001`, and
`PAIR-POSITIVITY-001`, without using `PAIR-BGSTB-001` as a premise.

At fixed \(T\geq3,1\leq X\leq T\), use \(R=L\), then divide the
resulting expression for \(2\pi\Phi\) by \(Tq\), where \(q=\log T>1\).
The four errors normalize as follows:

| Source error | Normalized bound |
| --- | --- |
| Prime-side peak error \(O(Tq/X^2)\) | \(O(X^{-2})\) |
| Remaining prime-side error \(O(T\sqrt q)\) | \(O(q^{-1/2})\) |
| Comparison \(O(T)\) | \(O(q^{-1})\) |
| Comparison \(O(X)\) | \(O(X/(Tq))\) |

Since \(X/(Tq)\leq q^{-1}\leq q^{-1/2}\), absorb the comparison
errors and substitute \(X=T^\alpha\) for \(0\leq\alpha\leq1\).
Negative \(\alpha\) uses exact evenness, not the prime-side estimate at
\(X<1\). Reality and nonnegativity on all of \(\mathbb R\) are already
proved by `PAIR-POSITIVITY-001`.

Both endpoints are included:
\(\mathcal F_T(0)=\log T+O(1)\) and
\(\mathcal F_T(\pm1)=1+O((\log T)^{-1/2})\).
The peak error cannot be discarded at zero. There is no new interchange:
the estimates hold uniformly even for \(\alpha=\alpha(T)\in[-1,1]\).
No extension beyond this closed interval is claimed.
The exact scale translation in §3 remains applicable.

Effectivity is inherited from the local input estimates; complete numerical
values of \(C_1,C_2\) are not supplied. The comparison retains published
computer-assisted zero-free-region and low-height inputs. No local
certificate or independent replay is claimed, and the remaining upstream
audit obligations are unchanged.

The standard-library script
`python3 -B scripts/check_pair_asymptotic.py`
checks both main-term coefficients, all four error scales, signed comparison
errors, rational-power substitutions including endpoints, and the elementary
absorption algebra. These are exact regression checks, not certificates
of the asymptotic or numerical evidence about zeta zeros.

Validation on 2026-09-28: all 43 exact regression tests passed (38 existing
and 5 normalization tests), using
`python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v`.
The 28-claim ledger passed unique-key/ID, dependency-resolution and
acyclicity checks, including source-node and reconstruction links.
The local theorem's dependency closure contains only `UNCONDITIONAL`
claims, retains the published computational inputs, and excludes the
imported headline theorem. Theorem-label mappings, references, citations,
local file links and Python syntax passed.
The manuscript compiled in an isolated temporary directory with pdfLaTeX,
BibTeX and two resolving LaTeX passes to a 23-page PDF, with no final-pass
warnings, unresolved references/citations, or overfull/underfull boxes.
