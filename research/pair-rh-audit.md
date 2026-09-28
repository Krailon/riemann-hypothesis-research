# Pair baseline: RH-contamination review

Task: exposition and proof review. Assumptions: `UNCONDITIONAL` for the
reconstruction; the explicitly isolated specialization checks use `RH`.
Reviewed 2026-09-28. Local claims retain status **`proved-draft`**.

## Finding and scope

**No RH contamination was found in the reviewed local proof or in the stated
hypotheses of its eight imported analytic inputs.** No unresolved local
passage was identified. This is a recorded review of the draft, not independent
mathematical verification or a formal proof certificate.

The [coverage record](pair-rh-audit.json) partitions all **1,737 lines** of
[the manuscript](../proofs/pair_baseline.tex) into **115 contiguous passages**.
Each passage has a classification, claim IDs, assumptions, a verdict and a
specific justification. Preamble, bibliography and whitespace are included
in the partition; mathematical paragraphs and their displays are reviewed
together. The review follows all **26 claims and four provenance nodes** in
the dependency closure of `PAIR-ASYMPTOTIC-001` (39 recorded edges).
`PAIR-TRANSLATION-001` is reviewed separately, giving 27 audited claims.
`PAIR-BGSTB-001`, the imported headline theorem, is outside the proof closure.

Supplemental coverage records identify the exact translation passages,
notation file and RH regression examples reviewed. Selected-passage records
do **not** claim a complete audit of those files. Whole-file SHA256 hashes
bind all line locators to the reviewed versions. The ledger is also hashed
and its relevant assumptions, dependencies, statuses and computational flags
are snapshotted. The record contains 123 passages in total.

## Local proof findings

| Passage IDs | Checked issue | Finding |
| --- | --- | --- |
| P002–P003, P013–P024 | Full zeros and counting | All occurrences and multiplicities are retained. Ordinate-only kernels are nonnegative bounds. The paired eta series excludes real nontrivial zeros analytically. |
| P025–P035 | Explicit formula | The evaluation variable `s=1/2+it` does not replace any zero. Euler/Fubini majorants, selected contour heights, residue multiplicities, ordered contour limits and endpoint cancellation are explicit. |
| P036–P041 | Uniform remainder estimates | Functional-equation differentiation takes place away from zeros/poles. Digamma and Euler-series bounds apply in their stated regions, including bounded `t`. |
| P042–P053 | Complex pair integral and squared norm | Both horizontal displacements survive conjugation and the line shift. The strip condition excludes crossing poles. Coincident poles may represent distinct reflected off-line zeros. Reflection permutes the complete occurrence sum, not its diagonals. |
| P054 | Positivity | Positivity follows from a finite squared L2 norm; evenness follows by exchanging indices. No RH-equivalent general positivity criterion is imported. |
| P055–P061 | Height truncation | The finite envelope applies only to retained zeros. Extensions enlarge unweighted positive bounds. Quadratic remainder and extension sign are kept. Small heights are bounded without a first-zero dataset. |
| P062–P066 | Finite-height envelope | The only unconditional substitution `delta=0` for actual zeros uses the published finite verification, for `0<|gamma|<3`. The thresholds `3` and `Z` use the inclusive KV theorem. Reflection supplies the other horizontal sign. |
| P067–P071 | Uniform comparison | Effective elementary absorption uses the established envelope. The `3<=T<5` case does not assume `T log^2 T>=2T`. |
| P072–P077 | Fourier mean value | Proved locally from sinc kernels, absolute coefficient sums and a signed lower majorant. The inaccessible Goldston–Montgomery result is not an imported premise. Transform continuity justifies the strict nearby-frequency cutoff. |
| P078–P091 | Arithmetic estimates | Upper-bound sieve and classical PNT suffice; proper prime powers and integer cutoffs remain included. No RH-strength PNT remainder or prime-pair asymptotic is used. |
| P092–P105 | Prime-side square and assembly | Absolute convergence justifies prime-series integrals. All residuals are bounded before combining; negative alpha uses evenness. Constants and ranges are uniform. |
| P106–P114 | Endpoints and checks | The peak error at alpha=0 remains O(1). Three RH specialization passages are isolated checks, never premises of the theorem. |
| T001–T003, N001–N002 | Exact conventions | Horizontal amplitude and complex Fourier argument remain. Compactly supported smooth test functions justify the entire extension; mere L1 is insufficient. The exact `q_T` scale and `C_T` normalization are preserved. |

The JSON reasons provide the finer passage-level accounting; the table above
is a navigation summary. In particular, unconditional positivity concerns the
**whole** pair sum, not each summand. Neither the proof nor its convention
translations infer simplicity, a purely vertical unweighted correlation
formula, a critical-line proportion, or a support extension for a later theorem.

### Conditional checks and wording correction

The manuscript's three marked RH specializations concern the explicit-formula
kernel, norm identity and truncation envelope. The translation note has one
additional marked RH check. The three selected regression methods specialize
finite rational or synthetic fixtures; their outputs are not analytic proof
inputs. Giving a fixture zero displacement makes no assertion about actual
zeros at arbitrary height.

The earlier sentence “RH is not used elsewhere” was too broad in a section
containing two further marked RH checks. It now says that the specialization
is not used in an unconditional proof. The closing scope paragraph now points
to this review. These edits change no theorem statement or proof argument.

## Imported-statement evidence

These are reviews of the **stated hypotheses and the local application**,
with nearby definitions and proof structure inspected where indicated.
They do not reconstruct every upstream proof. The JSON evidence IDs resolve
to the following sources and exact locators. Online sources were reopened
on 2026-09-28; remote contents are not archived or content-hashed by this audit.

| Evidence / claim | Source and reviewed boundary |
| --- | --- |
| `analytic` / `ZETA-ANALYTIC-001` | [DLMF §25.2](https://dlmf.nist.gov/25.2), [§25.4](https://dlmf.nist.gov/25.4), [§25.10(i)](https://dlmf.nist.gov/25.10): continuation, Euler product, functional equation, critical strip and symmetry. RH is separately identified as a hypothesis, not a fact. This is an authoritative reference rather than an original proof reconstruction. Multiplicity preservation follows locally from the nonvanishing functional-equation factor in the strip. |
| `countinput` / `ZETA-COUNT-001` | [Montgomery–Vaughan, Chapter 14](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/18.0_pp_452_462_Zeros.pdf), pp. 452,454: midpoint definition and Corollary 14.3, with O(log T). Adjacent Corollary 14.4 explicitly assumes RH and is excluded. The local proof supplies the inclusive endpoint translation. |
| `contour` / `ZETA-CONTOUR-001` | [Montgomery–Vaughan, Chapter 12](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/16.0_pp_397_418_Explicit_formulae.pdf), pp. 398–400: Lemmas 12.2 and 12.4 give selected heights and a left-half-plane logarithmic-derivative bound away from trivial zeros. Their hypotheses and surrounding proofs do not assume RH or simplicity. |
| `gamma` / `GAMMA-DIGAMMA-001` | [Montgomery–Vaughan, Appendix C](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/20.3_pp_520_534_The_gamma_function.pdf), pp. 523–524: Theorem C.1, equation (C.17), in a fixed sector away from the negative real axis. The Euler–Maclaurin argument gives an effective remainder, applicable to the local arguments with real part at least 3/2. |
| `kv` / `ZETA-KV-001` | [Mossinghoff–Trudgian–Yang, published Theorem 1.1](https://link.springer.com/article/10.1007/s40993-023-00498-y), equation (1.5): coefficient 55.241, inclusive height threshold 3 and zero-free boundary. Section 5 uses a proved finite-height verification; the theorem does not assume RH globally. Numerical ingredients are external proof dependencies. Other conditional improvement discussions in the article are not imported. |
| `low` / `ZETA-LOW-001` | [Platt–Trudgian, published abstract](https://doi.org/10.1112/blms.12460), and [arXiv v1, Theorem 1 and §2](https://arxiv.org/html/2004.09765v1): rigorous finite verification using Arb and a variation of Turing's method. Only the published range `0<gamma<=3*10^12` is imported, despite the larger height in v1. Simplicity is not imported. No project replay was performed. |
| `pnt` / `PRIME-PNT-001` | [Montgomery–Vaughan, Chapter 6](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/10.0_pp_168_198_The_Prime_Number_Theorem.pdf), pp. 179–181: Theorem 6.9 for all real x>=2, using the classical zero-free region, Perron truncation and contour shifting. This effective PNT does not rely on RH or the modern computational KV input. |
| `sieve` / `PRIME-SIEVE-001` | [Montgomery–Vaughan, Chapter 3](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/07.0_pp_76_107_Principles_and_first_examples_of_sieve_methods.pdf), p. 97: Corollary 3.14 explicitly gives uniformity in nonzero even shifts; Theorem 3.13 supplies the upper sieve. Take x=0, y=U and absorb the fixed product constant. The neighboring prime-pair asymptotic is a conjecture and is not used. |

The ledger's computational flags remain true for `ZETA-KV-001`,
`ZETA-LOW-001`, `PAIR-ENVELOPE-001`, `PAIR-COMPARE-001` and
`PAIR-ASYMPTOTIC-001`. They record inherited published computer-assisted
inputs. This review supplies no local numerical certificate or artifact hash
for those computations. The remaining claims in the local theorem closure
have no computational proof input.

## Structural validation and maintenance

Run from the repository root:

```bash
python3 -B scripts/check_pair_rh_audit.py
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v
```

The [checker](../scripts/check_pair_rh_audit.py) verifies hashes, complete
manuscript coverage without gaps or overlaps, unique record IDs, claim and
evidence references, imported-input coverage, the recorded dependency closure,
assumptions, and the classification of the three manuscript RH checks. It
rejects unresolved local passages and inconsistent outcome flags. Seven tests
include deliberate mutations of coverage, bytes, assumptions and references.
The ledger reader indexes this repository's current stable-ID/one-line-field
format; it fails on unsupported audited-field syntax and is not a general
YAML parser.

These checks detect a stale or structurally incomplete **review record**.
They do not evaluate whether a mathematical justification is true, fetch
remote sources, prove asymptotics, or establish independence of the review.
An edit to a reviewed file or the ledger requires re-review of affected
passages and dependencies before updating hashes or snapshots. Do not refresh
hashes merely to obtain a passing check. Changed conditional examples require
reviewing their use, even when their algebra still passes.

Validation on 2026-09-28: all **59 tests passed** (52 existing plus seven
audit checks). The manuscript rebuilt with `pdflatex`, `bibtex`, and two
further `pdflatex` passes: 23 pages, resolved references and citations, no
final-pass warnings or overfull/underfull boxes. Generated TeX files were
kept outside the repository.

## Remaining obligations

The JSON records these separately from local unresolved passages:

1. Independent mathematical review of the local reconstruction.
2. Full upstream foundational reconstruction; existing incomplete dependency
   graph flags and pending interchange audits retain their scope.
3. Independent reconstruction/replay of the published computer-assisted inputs.
4. Final journal-text comparisons for BGSTB and for PT beyond the checked
   published abstract.
5. A clean-checkout reproduction entry point and environment for Work Package A.

Completing this local RH-contamination review does not complete Work Package A
or upgrade any `proved-draft` claim to `independently-checked`.
