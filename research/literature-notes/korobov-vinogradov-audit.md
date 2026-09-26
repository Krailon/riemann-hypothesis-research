# Published Korobov–Vinogradov input: source audit

Task: exposition and source verification. Assumptions: `UNCONDITIONAL`.
Claim: `ZETA-KV-001`, an imported `published` theorem.
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

## Handoff to the finite-height argument

The source threshold does not cover \(0<|\gamma|<3\).
The next proof must address that range explicitly before using a bound on
every occurrence with \(|\gamma|\leq Z\). The PT result provides a
potential published low-height input, but its integration is not asserted
here. The existing exclusion of real zeros only covers \(\gamma=0\).

The eventual passage from a bound at each \(|\gamma|\) to one at \(Z\)
also requires the direction of monotonicity to be established. Neither
the envelope for \(B(Z)\) nor the uniform comparison of \(L(X,T)\) with
\(2\pi\Phi(X,T)\) is claimed by this source audit.

Accordingly, `BGSTB-ZFR` now has status
`primary_source_verified_application_pending`, linked through
`verified_input_claim: ZETA-KV-001`. It is not marked as a reconstructed
local proof, and the full pair theorem retains that unfinished dependency.

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
