# Work Package A closure checklist

Task: exposition and project-status bookkeeping. Assumptions: `UNCONDITIONAL`.
Status reviewed **2026-10-01** against [AGENTS.md §3](../AGENTS.md), the
[theorem ledger](theorem-ledger.yaml), and the artifacts below.

**Baseline reconstructed; final closure pending.** The root claim is
`PAIR-ASYMPTOTIC-001`, status `proved-draft`, with `PAIR-TRANSLATION-001`
providing the separate convention translation. Independent mathematical
review and a preserved reproduction record for the designated baseline
revision remain open. This checklist introduces no theorem or status upgrade.

## Required outputs

“Complete” below means the stated artifact exists within its recorded scope;
it does not mean independent verification of the analytic proof.
Proof labels refer to [pair_baseline.tex](../proofs/pair_baseline.tex).

| AGENTS.md requirement | Status | Evidence and claim locators | Verification boundary |
| --- | --- | --- | --- |
| 1. Dependency graph of every analytic input | Complete for the recorded local proof | [Dependency graph](dependency-graph.md); root `PAIR-ASYMPTOTIC-001`, 26 claims and four provenance nodes | Includes eight imported theorems; their upstream proofs are not fully reconstructed. Existing incomplete-dependency flags remain accurate. |
| 2. Every appearance of \(\beta\) visible | Complete in draft | [Full-zero translation](literature-notes/pair-baseline.md); `PAIR-TRANSLATION-001`, `PAIR-EF-001`, `PAIR-NORM-001`; `eq:zero-sum`, `eq:norm-pair-definition` | Retains complex zeros and multiplicities. RH specializations are isolated checks; reflection equates full sums, not diagonal subsets. |
| 3. Diagonal, prime/prime-power, archimedean and error decomposition | Complete in draft | [Named error budget](pair-error-budget.md) and [zero-diagonal bookkeeping](literature-notes/pair-baseline.md); `PAIR-PRIME-DIAGONAL-001`, `PAIR-RHS-MEAN-001`; `eq:prime-diagonal`, `eq:primepowers-diagonal`, `eq:pair-assembly` | Zero-index and prime-series diagonals are distinct. Proper powers and cross terms remain in the accounting; regressions check algebra, not estimates. |
| 4. Uniform estimates | Complete for the pair-baseline ranges | [Error budget](pair-error-budget.md); `PAIR-TRUNC-001`, `PAIR-ENVELOPE-001`, `PAIR-COMPARE-001`, `PAIR-RHS-MEAN-001`; `thm:pair-asymptotic` | Final range: \(T\ge3\), \(\lvert\alpha\rvert\le1\); mean square: \(1\le X\le T\). Endpoints and low heights are covered. No uniformity in future three-level smoothing parameters is claimed. |
| 5. Machine-checkable Fourier conventions and support | Complete | [Convention table](pair-conventions.json), [notation](notation.md), [checker](../scripts/check_pair_conventions.py); `PAIR-TRANSLATION-001`, `PAIR-MEANVALUE-001` | Exact signs, scales, domains and support boundaries are checked. The table does not certify analytic estimates or enlarge support. |
| 6. Line-by-line RH-contamination audit | Complete within the recorded scope | [Review](pair-rh-audit.md), [hashed record](pair-rh-audit.json), [checker](../scripts/check_pair_rh_audit.py); root and translation claims | Covers the local manuscript and imported-statement hypotheses. Independent review, full upstream proof reconstruction and external computational replay are separate. |

## Comparison and reproduction

- [x] **Accepted-text comparison:** [report](literature-notes/bgstb-accepted-comparison.md)
  covers the agreed Kyushu text, Theorem 1, its proof and the Fourier passage
  used locally. The two domain/exposition issues are already handled in our
  draft. Publisher-version verification is deferred and nonblocking.
- [x] **Reproduction harness implemented and exercised:**
  [entry point](../scripts/reproduce.sh), [instructions](../README.md#reproduce-the-pair-baseline).
  It regenerates main-term/error normalization records, runs the exact checks
  and builds the manuscript. It does not prove the imported analytic bounds.
- [ ] **Final revision sign-off:** preserve a full clean-checkout run for the
  designated baseline revision under the criteria below.

### Historical clean-checkout evidence

The manifest inspected on 2026-10-01 records a full run on 2026-09-28:

| Field | Recorded value |
| --- | --- |
| Source commit in the temporary validation checkout | `afc7b6e900a37dfb7ab4bb97a2421ca3eaa55c59` |
| Mode / result | `full` / `pass` |
| Working tree | `dirty: false`; empty Git status |
| Tests | 70 passed; no failures, errors or skips |
| PDF | 23 pages; no recorded failures or warnings |
| Manifest SHA256 | `f443efbdc6f98802ae51a9ef237e1856b8d368e498f1d8eccfafdfa55645960b` |

Its temporary location is
`/tmp/pair-clean-checkout-oof639b0/fresh clone/artifacts/reproduction/run-7zhf7ozt/manifest.json`.
This is historical harness evidence, not a durable release record or a run
of the later accepted-text-comparison revision. Temporary files may disappear.

## Two open closeout items

- [ ] **Independent mathematical review.** Record the reviewer, reviewed
  revision, claim coverage, findings and their resolutions in a durable report.
  Start with `PAIR-MEANVALUE-001` through `PAIR-RHS-MEAN-001` using the
  [prime-side audit](literature-notes/pair-prime-mean-audit.md), then cover the
  remaining root dependency closure and `PAIR-TRANSLATION-001`. Check uniform
  bounds, convergence, endpoint conventions and applicability of imported
  statements. Close this item only when no unresolved proof issue remains
  in that scope. Another pass by the original author and passing tests alone
  do not establish independence; any ledger promotion requires its own evidence.
- [ ] **Preserved full reproduction for the designated revision.** From a
  fresh checkout of that revision, run `./scripts/reproduce.sh` in full mode.
  Require `status: pass`, `source.dirty: false`, all expected tests passing
  (currently 70), generated normalization records and a successful PDF build
  with resolved references/citations. Review any recorded warnings. Preserve
  the manifest, logs, generated formulas and PDF at a durable location; record
  the source commit, location and manifest SHA256 here. A checks-only or dirty
  run does not satisfy this item. Changes affecting the proof or audited inputs
  after review must be reconciled before sign-off.

Writing this checklist closes neither item. They concern review and release
evidence; no additional baseline lemma was identified as missing by the
accepted-text comparison.

## Trusted inputs and deferred follow-ups

The reconstruction imports the following published inputs with their
stated hypotheses checked at use. The [dependency graph](dependency-graph.md)
and [RH-audit evidence](pair-rh-audit.md) provide exact source locators.

| Imported claims | Trusted input |
| --- | --- |
| `ZETA-ANALYTIC-001`, `ZETA-COUNT-001` | Analytic structure and symmetries; unconditional Riemann–von Mangoldt counting |
| `ZETA-CONTOUR-001`, `GAMMA-DIGAMMA-001` | Logarithmic-derivative contour estimates; fixed-sector digamma approximation |
| `PRIME-PNT-001`, `PRIME-SIEVE-001` | Effective classical PNT; uniform upper-bound sieve for prime pairs |
| `ZETA-KV-001`, `ZETA-LOW-001` | Published explicit KV region and finite-height critical-line verification; external computational provenance retained |

The imported BGSTB headline theorem is a comparison target, not a premise
of the local asymptotic proof. The needed Fourier mean-value bound is proved
locally rather than imported from the inaccessible GM87 text.

Deferred follow-ups are complete upstream re-proofs, replay of external
computer-assisted inputs, publisher-version checks, and broader uv/Nix/container
pinning and CI. They are not prerequisites for using these identified published
inputs in the present baseline. No local computational certificate is claimed.

Historical audit lists describe their own review dates. This checklist supplies
the current closure status without rewriting those records or changing proof
hashes, dependency-completeness flags, assumptions or theorem statuses.
