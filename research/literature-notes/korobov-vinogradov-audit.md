# Published Korobov–Vinogradov input: source audit

Task: proof, exposition and source verification. Assumptions: `UNCONDITIONAL`.
Claims: `ZETA-KV-001` and `ZETA-LOW-001`, imported `published`
theorems; `PAIR-ENVELOPE-001` and `PAIR-COMPARE-001`, local
`proved-draft` lemmas.
The project has checked the statement and inspected its proof structure;
independent proof reconstruction and computational replay are pending.
See the [ledger](../theorem-ledger.yaml) and
[manuscript input](../../proofs/pair_baseline.tex), label `inp:kv`.

## Exact primary source

Michael J. Mossinghoff, Timothy S. Trudgian and Andrew Yang,
*Explicit zero-free regions for the Riemann zeta-function*,
Research in Number Theory **10**, article 11 (2024), 27 pages.
Bibliography key: `MTY2024`.

The [publisher's version of record](https://doi.org/10.1007/s40993-023-00498-y)
was published on 12 January 2024. Theorem 1.1, equation (1.5), is on
page 2 of the [publisher PDF](https://link.springer.com/content/pdf/10.1007/s40993-023-00498-y.pdf).
The statement and publication metadata were checked on 2026-09-26.
This audit uses the published text, not an unversioned preprint.

For \(u\geq3\), define
\[
 \nu_{\rm KV}(u)=
 \frac{1}{(55241/1000)(\log u)^{2/3}(\log\log u)^{1/3}}.
\]
The imported theorem excludes zeros at every point satisfying
\[
 |t|\geq3,\qquad \sigma\geq1-\nu_{\rm KV}(|t|).
\]
Here \(55.241=55241/1000\) is the exact published constant.
The logarithms are natural and the powers are positive real powers.

| Convention | Checked interpretation |
| --- | --- |
| Height threshold | Both signs, with \(\lvert t\rvert=3\) included |
| Horizontal boundary | The boundary \(\sigma=1-\nu_{\rm KV}(\lvert t\rvert)\) is excluded as well |
| Zero formulation | Every zero with \(\lvert\gamma\rvert\geq3\) has \(\beta<1-\nu_{\rm KV}(\lvert\gamma\rvert)\) |
| Multiplicity | Nonvanishing excludes zeros of every multiplicity |
| Effectivity | The coefficient and starting height are explicit; no unspecified sufficiently-large threshold |
| Normalization | Physical imaginary height; no mean-spacing or Fourier conversion |

The strict inequality in the zero formulation is the complement of the
closed excluded region. It is not a boundary extension of a theorem stated
only on an open region. No claim about the best currently known constant
is needed for Work Package A.

## Proof structure and computational provenance

Section 5 proves Theorem 1.1 by separating low, intermediate and large
heights. It invokes a finite-height verification, the paper's Theorems 1.3
and 1.4, and analytic estimates near the line \(\Re s=1\).
Sections 8–9 discuss computational ingredients. Section 8 uses randomized
search to find polynomials; their nonnegativity is supplied by a
squared-modulus construction. Printed coefficients are rounded.
This source map does not certify the numerical inequalities.

The finite-height input is Platt–Trudgian, *The Riemann hypothesis is true
up to \(3\cdot10^{12}\)*, Bulletin of the London Mathematical Society
**53**(3), 792–797 (2021), bibliography key `PT2021`.
Its [publisher abstract and metadata](https://doi.org/10.1112/blms.12460)
were checked along with [arXiv:2004.09765v1](https://arxiv.org/pdf/2004.09765v1),
a **PREPRINT version of the published work**.
Theorem 1 of v1 actually states height 3,000,175,332,800; the dependency
used by MTY is the smaller \(3\cdot10^{12}\) range. Section 2 describes
Arb arithmetic and a variation of Turing's method. Full comparison of
that preprint with the final PT journal text is pending.

This is an established finite-range computational input, not an assumption
that RH holds at arbitrary heights. We have not downloaded a zero dataset,
repeated the computation, or replayed a certificate. The project's L2/L3
certification labels are not assigned to this unreplicated external input.
The ledger therefore sets `computation_used_in_proof: true`,
`certificate_artifact_hash: null`, and
`dependency_graph_complete: false` for `ZETA-KV-001`.
Upstream limit interchanges remain unaudited and are recorded as unknown.

The provenance nodes `MTY-KV-PROOF` and `PT-LOW-ZEROS` identify the
source-level dependencies; they are not additional locally proved claims.
Importing this theorem does not change the assumptions or dependencies
of the existing local Lemmas 1–4.

## Finite-height envelope — PAIR-ENVELOPE-001

The low-height input is now recorded separately as `ZETA-LOW-001`:
every zero occurrence with \(0<\gamma\leq H=3\cdot10^{12}\) has
\(\beta=1/2\). This inclusive statement was checked again against the
published abstract on 2026-09-26. Only \(0<|\gamma|<3\) is needed here;
conjugation supplies negative ordinates. No simplicity assertion is used.

For \(u\geq3\), logarithmic differentiation gives
\[
 \frac{\nu_{\rm KV}'(u)}{\nu_{\rm KV}(u)}
 =-\frac{2}{3u\log u}
  -\frac{1}{3u\log u\log\log u}<0.
\]
The proof bounds \(\log3>13/12\) and \(\log\log3>1/13\) by elementary
integrals. Together with \(55241/1000>5\), these show
\(\nu_{\rm KV}(3)^{-3}>125/13>8\), hence
\(0<\nu_{\rm KV}(Z)<1/2\) for every \(Z\geq3\).
All constants are exact; no numerical approximation is needed.

Fix \(Z\geq3\). The height cases in the proof are:

| Height | Input and conclusion |
| --- | --- |
| \(\gamma=0\) | The existing `PAIR-COUNT-001` proof excludes nontrivial real zeros. |
| \(0<\lvert\gamma\rvert<3\) | `ZETA-LOW-001` and conjugation give \(\delta_\rho=0<1/2-\nu_{\rm KV}(Z)\). |
| \(3\leq\lvert\gamma\rvert\leq Z\) | KV and decreasing \(\nu_{\rm KV}\) give \(\delta_\rho<1/2-\nu_{\rm KV}(\lvert\gamma\rvert)\leq1/2-\nu_{\rm KV}(Z)\). |

Every entry of the finite maximum defining \(B(Z)\), including its
auxiliary \(0\), is strictly below the same positive bound. Therefore
\[
 B(Z)<\tfrac12-\nu_{\rm KV}(Z),\qquad
 \eta_*(Z)>\nu_{\rm KV}(Z).
\]
Strictness uses finiteness, not an assertion about an infinite supremum.
The empty-set case gives \(B(Z)=0\); multiplicities do not affect the
maximum. Both cutoff endpoints retain full weight. Reflection
\(\rho\mapsto1-\bar\rho\) gives
\(|\delta_\rho|\leq B(Z)<1/2-\nu_{\rm KV}(Z)\).
There is no local limit interchange or Fourier/mean-spacing conversion.

Thus \(\eta(Z)=\nu_{\rm KV}(Z)\) is an explicit admissible envelope for
Lemma 4, including at \(Z_*=T\log^2T\geq3\) for \(T\geq3\).
The manuscript label is `lem:pair-envelope`.
Its local proof is analytic; its ledger computational flag is true
because it depends on published computer-assisted inputs. No local
certificate, replay, or independent proof check is claimed.

## Uniform comparison — PAIR-COMPARE-001

The manuscript's `lem:pair-compare` derives, uniformly for
\(T\geq3\) and \(1\leq X\leq T\),
\[
 L(X,T)=2\pi\Phi(X,T)+O(T)+O(X).
\]
This reconstructs [BGSTB, arXiv:2306.04799v1, (2.18)](https://arxiv.org/html/2306.04799v1#S2),
the **PREPRINT version of the published work**. Final journal comparison
and independent review remain pending.

Put \(Z_*=T\log^2T\), \(\nu=\nu_{\rm KV}(Z_*)\), \(y=\log T>1\),
and \(z=\log Z_*=y+2\log y>1\). Since \(0<1-2\nu<1\),
\[
 X^{1-2\nu}\log^3T\leq T y^3e^{-2\nu y}.
\]
The proof establishes \(z\leq3y\) and \(\log z\leq\sqrt z\).
For the second inequality, the minimum of \(\sqrt v-\log v\) on
\([1,\infty)\) occurs at \(v=4\) and equals \(2-2\log2>0\).
With \(c_{\rm KV}=55241/1000<56\), this gives
\[
 2\nu y\geq
 \frac{2}{c_{\rm KV}3^{5/6}}y^{1/6}\geq y^{1/6}/84.
\]
Taking \(r=y^{1/6}/84\) and using Taylor's theorem
\(e^r\geq r^{18}/18!\), one obtains the global bound
\[
 y^3e^{-2\nu y}\leq18!\,84^{18}.
\]
This large auxiliary constant establishes effectivity; the full comparison
also contains the effective constants from Lemma 4. No numerical evaluation,
asymptotic threshold, or optimization enters the local argument.

For \(T\geq5\), the existing cutoff condition \(Z_*\geq2T\) holds.
Truncation contributes \(O(X)\), while height removal and integral
extension each contribute \(O(T)\); the extension retains its nonpositive
sign. For \(3\leq T<5\), the existing direct \(O(X)\) comparison supplies
the claim. The bound therefore covers \(X=1\), \(X=T\), \(T=3\), and
the transition at \(T=5\), preserving all zero endpoint and multiplicity
conventions. No new limit interchange is needed.

The `BGSTB-ZFR` source node now has status `reconstructed_draft`,
linked to `PAIR-COMPARE-001` as its local claim. The full pair theorem's
dependency list uses that claim and retains `BGSTB-MEAN` as unresolved.
The comparison and the full theorem's reconstructed dependency chain carry
the imported computational provenance; no local certificate or replay is
claimed. The next task is the prime-side mean square, followed by assembly
of the full pair asymptotic.

## Validation

Acceptance checks are agreement of the manuscript and ledger with the
published statement, unique/resolved claim and bibliography IDs, an acyclic
dependency graph, and a successful bibliography/reference-resolving PDF build.
No numerical test is offered as verification of the zero-free theorem.

These checks passed on 2026-09-26, including duplicate-YAML-key detection,
exact rational interpretation of the constant, and computational-provenance
flags. The combined manuscript compiled to 14 pages with `pdflatex`,
`bibtex`, and resolving LaTeX passes. The final log has no warnings,
unresolved citations/references, or overfull/underfull boxes. Existing
mathematical regression scripts were unchanged; this task introduced no
new numerical algorithm or proof certificate.

After adding the finite-height proof on 2026-09-26, the structure checks
passed again for all 19 claims, including dependency edges through the
source-node links and the two new claims' computational-provenance flags.
The 28 existing exact regression checks passed (8 for Lemma 1, 11 for
Lemma 3, and 9 for Lemmas 2/4). They remain algebra checks.
The rational comparisons in the analytic logarithm bound were also
checked exactly; no numerical evaluation of a logarithm was used.
The updated manuscript compiled to 15 pages with resolved bibliography
and references, no final-pass warnings, and no overfull/underfull boxes.
The build used pdfLaTeX, BibTeX, and two resolving LaTeX passes in an
isolated temporary directory. Independent mathematical review remains
pending.

After adding the uniform comparison on 2026-09-26, all 28 existing
regression checks passed again. Exact rational checks confirmed the
auxiliary exponent identities \(2/3+(1/3)(1/2)=5/6\),
\(1-5/6=1/6\), \(18/6=3\), and the coarse constant
\(2/(56\cdot3)=1/84\). These checks supplement the analytic proof;
they are not numerical certificates.
Structure and provenance checks passed for all 20 claims, including the
new comparison dependency in the full pair theorem and the preserved
unresolved prime-side input. The combined PDF compiled to 16 pages with
pdfLaTeX, BibTeX, and two resolving LaTeX passes; the final log has no
warnings, unresolved references/citations, or overfull/underfull boxes.
