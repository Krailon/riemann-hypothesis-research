# Work Package B: line-by-line RH-contamination audit

Task: exposition and proof review. Reviewed **2026-10-03**.
The local proof is `UNCONDITIONAL` with the individual stated support
restrictions. The isolated all-zero critical-line interpretation uses `RH`;
synthetic verification fixtures are classified separately.

## Finding and scope

**No RH contamination was found in the reviewed local manuscript or in its
applications of the inherited inputs. No unresolved analytic gap was
identified in this review.** One editorial notation error was corrected:
the assembled theorem's prose definition of the profile had three literal
`epsilon` strings; these now use the LaTeX `\epsilon` command. The kernel,
assumptions, normalization, errors and ledger statements are unchanged.

The [coverage record](triple-rh-audit.json) partitions every line of the
[triple manuscript](../proofs/triple_explicit_formula.tex), including its
preamble, tables, contextual remarks and closing material. It covers all
**18 triple claims**, including the three intermediate results outside
the final theorem's dependency closure. The combined review scope contains
**34 claims, two provenance nodes and 64 dependency edges**. The
[assembled-theorem graph](triple-dependency-graph.md) retains its narrower
31-claim, 58-edge scope.

This is an authored review of the draft, not independent mathematical
verification, a formal proof certificate, or a numerical certificate.
All local claims retain **proved-draft** status. The checker validates
coverage, freshness and classification consistency; it cannot certify
the mathematical correctness of the recorded reasons.

## Findings by proof stage

| Manuscript lines | Checked issue | Finding |
| --- | --- | --- |
| 20–324 | Full zeros, explicit formula, diagonals and endpoints | All occurrences and both ordinate signs are retained; evaluating an explicit formula on a vertical line does not restrict the zeros. Absolute kernel/prime majorants justify Fubini and the five index partitions. Reflection is a reindexing, not termwise invariance or a simplicity assertion. |
| 325–634 | Uniform norms and remainder budget | Positivity is that of the prescribed smoothing measure and squared norms. The inherited mean square is applied only for `x<=2T`; no general zero-statistic or Weil positivity is assumed. All four remainder components retain their norms. |
| 635–909 | Logarithmic gaps and off-diagonal estimates | Ordered integer frequencies are combined before the gap estimate. Elementary convolution, dyadic bounds and integration by parts suffice; no prime-pair/triple asymptotic is imported. The interior consequence is additive with a fixed positive margin. |
| 910–1194 | Retained terms and interior Fourier tests | Classical PNT includes proper prime powers. Stieltjes endpoints and tails are explicit. Complex test arguments retain sums of horizontal displacements; their bound follows from compact Fourier support, not real-plane Schwartz decay. |
| 1195–1502 | Origin and axis boundary layers | Integrated errors precede passage to the limit. One-sided traces and origin/ray masses are preserved. The quadrant inverse transform is correctly allowed to be non-Schwartz. No outer support boundary is added. |
| 1503–1742 | Signed sectors | Reciprocal reflection uses all occurrences and absolute convergence. Negative sectors conjugate the test as well as the statistic. Adjacent sectors each contribute their limiting ray mass; coordinate line measure has no arclength factor. |
| 1743–2004 | Full-gap kernel and localization | Pole separation and dominated convergence include collisions. Summability comes from the separate near/far decomposition, not the tuplewise estimate alone. Both signs of ordinates and horizontal dependence survive profile replacement. |
| 2005–2108 | Critical-line specialization | Zero-delta kernel evaluation is an unconditional parameter calculation. The all-zero interpretation is explicitly isolated as requiring RH and is not used in the proof. The microscopic expansion is never substituted into the unrestricted infinite sum. |
| 2109–2310 | Sine benchmark and cumulants | The determinant and five partitions are handled as deterministic distributions. No external zeta correlation theorem is imported. The ordinary benchmark cumulant cancellation does not assert a weighted zeta cumulant identity; the factorial cycle is nonzero. |
| 2311–2470 | Assembled theorem | Exact normalization is `(2/3)A_T^J`, with coefficient `16/(3T log T)`. Both error norms and the positive support margin persist. The result is an additive weighted full-zero theorem, including zero main terms. |

## Inherited evidence and assumption separation

The review reuses the [Work Package A audit](pair-rh-audit.md) for
**16 inherited claims**, with their original passage IDs and six imported
source-evidence records. Its source hashes and snapshots were validated.
The local uses of the explicit formula, zero counts, prime mean square,
PNT and sieve were checked against the stated ranges. This does not
re-review every line of the pair manuscript or replay its external sources.
The five unknown upstream interchange fields remain unknown.

The classical PNT and uniform upper-bound sieve occur in this dependency
chain. The pair asymptotic, modern computational KV theorem and finite-height
zero verification do not. The recorded Conrey–Snaith source supplies only
benchmark conventions; the local Fourier proof does not invoke its zeta
theorem. No new external analytic premise was discovered, and no fresh
external-literature verification is claimed.

The audit record distinguishes:

- **Parameter specialization:** zero horizontal kernel parameters or a tuple
  already known to lie on the line; assumptions remain unconditional.
- **Conditional interpretation:** extending that specialization to every
  zero tuple; marked `RH`, isolated and unused as a premise.
- **Verification fixtures:** finite quartet-symmetric data, including
  off-line displacements and repetitions; tagged `SYNTHETIC_MODEL`, never
  evidence for actual zeros or an asymptotic proof.

Supplemental records review selected passages of the theorem overview,
kernel and comparison notes, source note, sector table, and fixture
headers/constructor. Their whole-file hashes bind the selected ranges;
they do not claim complete reviews of those supporting files or scripts.

## Correction and limitations

Finding **F001** is editorial and resolved at manuscript line 2352.
Its before/after text and original source hash are retained in the JSON.
There were no RH-contamination findings requiring a mathematical correction,
and no change to theorem status, dependencies, assumptions or constants.
The manuscript still requires the full horizontal profile and complex test
arguments. Kernel removal, ordinary unweighted correlations and horizontal
consequences are not conclusions of this audit.

Upstream foundational reconstruction and independent review retain their
existing scope as nonblocking follow-ups; this audit introduces no new
approval or independent-review requirement. Work Package B remains open
for its clean-checkout reproduction harness.

## Coverage and verification

The record contains **161 reviewed passages across 15 files**: **141
contiguous passages covering all 2,470 manuscript lines**, and 20 selected
supporting passages. It records two isolated conditional interpretations
(manuscript and scope table), four parameter-specialization passages,
one resolved editorial finding, and no unresolved findings.

Run the [coverage checker](../scripts/check_triple_rh_audit.py):

```bash
python3 -B scripts/check_triple_rh_audit.py
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py'
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py'
```

The checker rejects gaps, overlaps, unreviewed tails, stale source/ledger/graph
hashes, lost support assumptions, missing inherited evidence, invalid claim
attribution, misclassified conditional passages, and false coverage claims.
Unresolved findings can be retained in a structurally valid record, but they
cannot coexist with a clean outcome or pass the default clean-audit check.

Validation on **2026-10-03**: all **96 triple checks**, including seven
audit checks, and all **70 pair checks** passed. The **34-page** triple
manuscript compiled in three `pdflatex` passes with shell escape disabled;
the final pass had no warnings, unresolved references, or overfull/underfull
boxes. These runs validate finite regression and audit metadata; they
are not a clean-checkout reproduction run or an analytic proof certificate.
