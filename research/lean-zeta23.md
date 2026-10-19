# Zeta23 import audit

Assumptions: `UNCONDITIONAL`. Source: Anthropic's
[formal-math, pinned commit e1a4e650](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/zeta23).
This is a source-code audit and selected port, not verification of the entire repository
or a new critical-line proportion theorem.

## Statements and dependency boundaries

| Surface | Exact boundary | Project decision |
| --- | --- | --- |
| `RHLinalg.rank_trace_ineq` | Finite matrices; P positive semidefinite, Q Hermitian, rank(P) ≤ r, positive index(Q) ≤ b, c > 0. No zeta input. | Import the four-module linear algebra closure and wrap for complex matrices. |
| `Zeta23.RvM.riemannVonMangoldt` | Takes `hΓ : GammaFacts`; its name alone does not certify an unconditional theorem. Returns dyadic main term and two-sided local upper counts for actual zeta zeros. | Import and apply to the proved `Zeta23.gammaFacts`. |
| `Zeta23.gammaFacts` | Closed theorem proving all nine fields, including Stirling, derivative and integral estimates. | Import its complete proof closure. No Gamma hypothesis remains in project wrappers. |
| `RvM.rvM_main_param` | Requires horizontal/vertical contour bounds, local counting, and Gamma integral/growth estimates. | All are discharged by `rvM_main` and `gammaFacts`; no parameter theorem is presented as an unconditional endpoint. |
| `PaperInputs Z` | A Prop-valued bundle: explicit formula, RvM, Chebyshev–Mertens, Hilbert inequality, Gamma. It is not a Lean axiom declaration. | Inspect assumptions in theorem types as well as `#print axioms`; merely passing an axiom check does not discharge these fields. |
| `Unconditional.lean`, `Final.lean`, main challenge | Larger headline-theorem assembly, separate from the selected roots. `Unconditional.lean` retains weaker 1/2-simple and 3/4-distinct wrappers while the README advertises stronger endpoints elsewhere. | Do not infer an exact theorem from the README. No headline proportion theorem is imported or checked in this milestone. |
| `PairCeiling.ceiling_law256*` | Explicit `EnclOK` enclosure premise, regularity hypotheses and certificate-validity inequality. Signed version also requires `0 ≤ r 1`. | Candidate for Work Package E only after checking the enclosure and matching our admissible class; not an unconditional numerical certificate here. |
| Dirichlet and ξ′ modules | Different zero objects and large additional dependency closures. | Outside this import. |

The imported `Statement.lean` contains RH-conditional sanity lemmas, but neither
project endpoint uses them. No RH, simplicity, pair-correlation conjecture, or
unstated analytic package is an argument of the dyadic endpoint.

## Exact conventions

`occurrenceWindow a b` contains **all multiplicity indices** of actual strip zeros
with `a < γ ≤ b`. Its cardinality is proved equal to Zeta23's `Ncount a b` for
all real a,b, including `b ≤ a` (empty). Analytic multiplicity is the same
`analyticOrderAt riemannZeta ρ |>.toNat` on both sides. No replacement of β by 1/2
occurs. There is no Fourier transform in these imported statements.

For `a ≤ b`, the exact endpoint correction is

```
#occurrenceInterval a b = #occurrenceWindow a b + #occurrenceInterval a a.
```

The last term counts every occurrence at the lower ordinate, including several
distinct complex zeros and repeated zeros. The existing logarithmic local count
bounds this atom; it is not assumed zero. Consequently both `(T,2T]` and `[T,2T]`
satisfy, for some C > 0 and T₀ ≥ 3, and **every real T ≥ T₀**,

```
|N - T/(2π) (log(T/(2π)) + 2 log 2 - 1)| ≤ C log T.
```

Constants and threshold are existential. These wrappers do not establish a sharp
cumulative `N(0,T]` remainder. Summing dyadic O(log T) remainders alone costs
O((log T)²), so a cumulative O(log T) claim requires another argument.

For finite complex matrices, `matrixPositiveIndex hQ` counts positive eigenvalues
with multiplicity and `matrixFrobeniusSq A = Re trace(A* A)`. The imported inequality is

```
c tr(P) - c² r/4 + 2c tr(Q) - c² b ≤ ||P+Q||²_F.
```

The c=2 consequence and dimension-zero endpoint are included. This supplies a
finite tool for Work Packages D/E; applying it to a zeta Gram construction still
requires that construction and its trace estimates.

## Port and provenance

The three roots select 45 original modules (13,758 lines). Exact upstream copies,
Apache 2.0 LICENSE, NOTICE, original toolchain and Lake metadata are preserved in
`vendor/zeta23/`. `manifest.json` binds every original and ported source by SHA256;
`compatibility.patch` records every change. `scripts/check_zeta23_import.py`
checks hashes, the exact original import closure, file coverage, metadata and patch.

The project retains Lean v4.34.1 and its existing OAI/mathlib pins. Upstream uses
v4.33.0-rc2 and mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.
Compatibility changes:

- Explicit `autoImplicit true` for upstream modules, whose proofs use that convention.
- Eleven `FromPNTPlus` forwarding modules reuse the project's existing
  `PrimeNumberTheoremAnd` definitions, avoiding duplicate global declarations.
  `StrongPNTPrefix` forwards to `StrongPNT`. These are substitutions of dependencies,
  not claims that the underlying files are byte-identical.
- Three product-log-derivative rewrites use the current `logDeriv_fun_mul` API.
- Upstream's `LieAlgebra.toModule` instance-priority adjustment is retained.
  A combined project build checks coexistence with the existing imports.

Original copyright notices remain available with every original file; forwarding
modules identify the original location. The pinned source is the provenance of
these imported proofs, not evidence of novel mathematics in this project.

## Verification and limits

The inventory lists nine public adapter theorems. Eight have Comparator challenges
that import only project definitions, not Zeta23 proof modules. The ninth is the
conversion to upstream `Ncount`; it is checked by Lean, the axiom report, and its use
inside the compared dyadic theorem. Four upstream endpoints also have axiom reports.
The permitted axioms are only `propext`, `Classical.choice`, `Quot.sound`.
An unfinished dyadic solution must be rejected for `sorryAx`.

Run on prepared project dependencies:

```bash
python3 -B scripts/reproduce_lean.py --skip-bootstrap --zeta23-only
```

This checks provenance, builds the imports and combined project, runs the two new
Comparator suites, rejects the unfinished proof, checks the complete project axiom
report, and runs coverage and pair/triple regressions. Earlier Comparator suites
are not rerun in this mode. The default harness includes all suites and dependency
preparation. Both modes archive hashes, logs and actual dependency patches. NanoDa
is disabled, consistently with existing milestones; no independent kernel check
is claimed. The record is a local build, not a fresh-checkout claim.

No selected statement proves cancellation in the signed complex-argument triple
error. `ORDINATE-ARGUMENT-VANISHING-001` and the conventional ordinate-only triple
asymptotic remain open. The next correlation-formalization step remains the
zero-side comparison and normalized pair asymptotic; dyadic counting is now a
reusable input.
