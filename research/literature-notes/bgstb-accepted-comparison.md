# BGSTB accepted-text comparison

Task: exposition and source verification. Assumptions: `UNCONDITIONAL`.
Reviewed **2026-10-01**. Claims: `PAIR-BGSTB-001`, `PAIR-TRANSLATION-001`,
`PAIR-ASYMPTOTIC-001`, and the local inputs mapped below.

**Completed for the agreed source:** the Kyushu repository manuscript,
designated by the user as sufficient accepted text for this comparison.
The main term, normalization and final error scales agree with our
reconstruction. Two domain/exposition issues are already handled locally;
this review requires no mathematical change. Publisher-version verification
is deferred and is not a prerequisite for continuing Work Package A.
Local claims remain `proved-draft`; this is not independent verification.

## Source and provenance

[Kyushu PDF](https://catalog.lib.kyushu-u.ac.jp/opac_download_md/7377443/7377443.pdf),
[repository handle](https://hdl.handle.net/2324/7377443), BGSTB,
*An unconditional Montgomery theorem for pair correlation of zeros of the
Riemann zeta-function*, [DOI](https://doi.org/10.4064/aa230612-20-3).
The cover records Acta Arithmetica **214** (2024), 357–376.
The downloaded file has 14 PDF pages: one repository cover followed by
manuscript pages 1–13, retaining the arXiv-v1/date markings. The acceptance
designation above records the agreed project scope, not an independently
verified repository version field.

**All page numbers below are manuscript numbers**; add one for the PDF viewer.
Theorem 1 is on p. 1; its proof occupies §2, pp. 2–6; the relevant Fourier
passage is on p. 6. These are actual locators in the downloaded copy.

## Short discrepancy table

| Topic | Source locator | Our reconstruction | Assessment/action |
| --- | --- | --- | --- |
| Hypotheses | Theorem 1, (1.2)–(1.4), p. 1; §2, pp. 2–6 | `thm:pair-asymptotic`: full complex zeros, multiplicity and all ordered pairs; no RH, simplicity or zero-density hypothesis. | **Equivalent.** Conditional applications in Theorems 2–3 are outside the imported baseline. |
| Normalization | (1.2)–(1.3), p. 1; (2.1), (2.6)–(2.8), pp. 3–4 | `eq:norm-pair-definition`, `eq:pair-norm`: \(w(z)=4/(4-z^2)\), \(\Phi=(2/\pi)\int|V|^2\); \(\mathcal F_T=\Phi(T^\alpha,T)/C_T\), \(C_T=T\log T/(2\pi)\). | **Equivalent.** Local reflection applies to the full occurrence sum, not diagonal subsets. The exact conversion is \(C_T=q_TTL_T\), with \(q_T=\log T/\log(T/(2\pi))\) for \(T>2\pi\). |
| Endpoints | (1.2), (1.4), p. 1; Lemma 1, p. 3; Lemma 4, pp. 4–5; before (2.19), p. 6 | `prop:ef-exact`, `lem:pair-trunc`, `lem:rhs-mean`: \(X=1\), prime powers counted once, full height-cutoff weights, bounded \(3\le T<5\) handled separately. | **Additional local justification.** The printed \(0\le x\le T\) before (2.19) is a **substantive domain discrepancy** at zero. Our required range is \(1\le X\le T\). Closed \(\alpha\in[0,1]\) agrees; evenness supplies \([-1,0]\). |
| Error terms | (2.2), (2.13)–(2.19), pp. 3–6; (1.4), p. 1 | `eq:pair-normalization` preserves \(O(X^{-2}),O((\log T)^{-1/2}),O((\log T)^{-1}),O(X/(T\log T))\) before absorption. | **Equivalent final scales; additional local justification.** The [named budget](../pair-error-budget.md) proves uniform absorption on \(1\le X\le T\), retaining the peak error at \(\alpha=0\). Effectivity is established locally; numerical constants are not asserted. |
| Source changes | Downloaded Kyushu manuscript versus [arXiv v1](https://arxiv.org/pdf/2306.04799v1), including references | All 13 manuscript pages have exactly equal extracted text after omitting the Kyushu cover. | **Equivalent extracted text.** No textual revision found in this comparison. Our source substitutions are documented below; this finding does not compare either file with an unexamined publisher version. |

Labels refer to [pair_baseline.tex](../../proofs/pair_baseline.tex).
The normalized local result is
\[
\mathcal F_T(\alpha)=T^{-2|\alpha|}\log T+|\alpha|
 +O(T^{-2|\alpha|})+O((\log T)^{-1/2}),
\qquad T\ge3,\quad |\alpha|\le1.
\]
No purely vertical unweighted theorem or horizontal proportion follows from
this comparison alone.

## Proof coverage and local justifications

Every passage in §2 was inspected against the corresponding local proof and
existing audit. The entries distinguish reconstruction choices from source
revisions; they do not claim to reverify every upstream cited theorem.

| Source passage | Local claims / proof labels | Comparison result |
| --- | --- | --- |
| Reflection (2.1), p. 3; theorem opening, p. 5 | `PAIR-POSITIVITY-001`; `cor:pair-positivity` | Same symmetry/norm mechanism. The occurrence permutation preserves multiplicities and positive heights. |
| Lemma 1, (2.2)–(2.3), p. 3 | `PAIR-EF-CONVERGENCE-001`, `PAIR-EF-EXACT-001`, `PAIR-EF-001`; `lem:ef-convergence`, `prop:ef-exact`, `lem:pair-ef` | Direct combined Mellin contour replaces subtraction of separate Landau sums. Absolute/local uniform convergence, limit order, prime-power endpoints and \(X\downarrow1\) are explicit. Combining the four local remainders recovers (2.2). |
| Lemma 2, (2.4)–(2.5), p. 3 | `PAIR-COUNT-001`, `PAIR-COUNT-KERNEL-001`; `lem:pair-count`, `lem:count-kernel` | Same counting input, with midpoint-to-inclusive translation and both-sign kernel bounds supplied locally. The proof excludes real nontrivial zeros, so the source's later \(0\le\gamma\) notation does not add occurrences. |
| Lemma 3, (2.6)–(2.8), pp. 3–4 | `PAIR-NORM-INTEGRAL-001`, `PAIR-NORM-001`; `lem:norm-integral`, `lem:pair-norm` | Same integral and coefficient. Our proof supplies integrability, the off-line contour shift, coincident-pole case and explicit tail. Reflection does not equate the original and reflected diagonal subsets. |
| Envelope and Lemma 4, (2.9)–(2.16), pp. 4–5 | `PAIR-TRUNC-001`; `lem:pair-trunc` | Our finite maximum includes the empty set; only retained weights use its horizontal bound. The quadratic truncation remainder and extension sign are explicit. The choice \(Z=T\log^2T\) is used with \(Z\ge2T\) for \(T\ge5\); smaller heights use a direct bound. |
| KV absorption and (2.18), p. 6 | `PAIR-ENVELOPE-001`, `PAIR-COMPARE-001`; `lem:pair-envelope`, `lem:pair-compare` | Same final comparison. Local inputs `ZETA-KV-001` and `ZETA-LOW-001` specify the constant, boundaries and \(0<|\gamma|<3\). Published computational provenance remains recorded. |
| (2.17)–(2.19) and remark, pp. 5–6 | `PAIR-MEANVALUE-001`, `PAIR-RHS-MEAN-001`, `PAIR-ASYMPTOTIC-001`; `lem:pair-meanvalue`, `lem:rhs-mean`, `thm:pair-asymptotic` | Local Fourier majorants, published PNT/sieve inputs, proper powers and cross terms recover the mean square. We do not import an unchecked GM87 lemma. Dividing by \(T\log T\) and setting \(X=T^\alpha\) gives the matching theorem. |

### Two domain issues and their disposition

1. **Mean-square endpoint:** p. 6 before (2.19) includes \(x=0\), where
   \(x^{-2}\) and \(\log x\) are undefined. Affected local claim:
   `PAIR-RHS-MEAN-001`. Its existing \(1\le X\le T\) domain suffices for
   `PAIR-ASYMPTOTIC-001`; no local correction is needed. No assertion for
   \(0<X<1\) is imported.
2. **Complex Fourier evaluation:** p. 6, (3.1) and the following sentence,
   overstate what follows from arbitrary \(g\in L^1(\mathbb R)\).
   Affected local claim: `PAIR-TRANSLATION-001`. Our existing
   \(g\in C_c^\infty\) convention supplies absolute convergence and an
   entire extension. Compact support also appears in the source's following
   Lemma 5; the broad introductory sentence does not invalidate Theorem 1.
   See the [translation audit](pair-baseline.md#3-exact-fourier-and-scale-translation--pair-translation-001).

Neither issue leaves an unresolved mathematical dependency in the local
comparison. Independent review, upstream reconstruction and computational
replay retain their existing statuses. Historical notes still saying journal
comparison is pending refer to their stated review dates and to the publisher
version; this report completes the narrower source comparison agreed here.

## File identification and extraction check

Both PDFs were downloaded on 2026-10-01. SHA256 of the actual PDF bytes:

- Kyushu: `79e68a339842642764467a806bd335d5bbdffc5ae4247729ab98ec7834a3aa54`.
- arXiv v1: `133071c4d85c875fe9b1a7d4001f22d7174270ab8f1fa8e6cee6178d20276ee9`.

Using `pypdf==5.9.0`, compare `extract_text()` for Kyushu pages `[1:]`
with arXiv pages `[:]`, preserving page order and all extracted characters:
**13 of 13 page strings match exactly**, without whitespace normalization.
The UTF-8 SHA256 of those manuscript strings joined by form feed (`\f`) is
`2eb1872a4ded3a2f90b7792865409381c297a228072f284f71908394649018fe`.
This checks extracted text, not binary or visual identity, and is not a proof
certificate. The reader was installed temporarily; project dependencies are
unchanged. Downloads and extraction files are temporary; URLs and hashes
identify the inputs for a repeat check.
