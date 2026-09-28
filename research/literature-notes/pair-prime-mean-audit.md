# Prime-side mean square: reconstruction and audit

Task: proof and source verification. Assumptions: `UNCONDITIONAL`.
Local claims have status `proved-draft`; independent review is pending.
See the [manuscript](../../proofs/pair_baseline.tex),
[ledger](../theorem-ledger.yaml), and [notation](../notation.md).

## Target and exact expression

For \(T\geq3\), \(1\leq X\leq T\), the reconstructed result is
\[
 R(X,T)=TX^{-2}\log^2T+T\log X+
 O(TX^{-2}\log T)+O(T\sqrt{\log T}).
\]
Here \(R=\int_0^T|-\mathcal P+A+H|^2dt\),
\(A=X^{-1}\log(t+2)\), and \(H\) is the sum of the four **exact**
remainders in `PAIR-EF-001`. In particular the expression inside
the norm is an equality, not an unspecified big-O function.
The existing explicit formula gives \(R=L\).
This is the prime-side content of BGSTB (2.17), (2.19), in
[arXiv:2306.04799v1](https://arxiv.org/html/2306.04799v1#S2), a
**PREPRINT version of the published work**. Final journal comparison
remains pending.

## Primary inputs and the Goldston–Montgomery citation

Two inputs are imported from the existing `MV2007` bibliography entry.
Their statements and proof structure were checked on 2026-09-26.

- `PRIME-PNT-001`: Theorem 6.9, (6.12)–(6.13), p.179 of the
  [author-hosted publisher chapter](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/10.0_pp_168_198_The_Prime_Number_Theorem.pdf).
  Its effective classical exponential-error PNT is unconditional.
  The proof on pp.180–181 uses the classical zero-free region; this
  dependency does not use the project's computer-assisted KV input.
- `PRIME-SIEVE-001`: Corollary 3.14, p.97 of the
  [author-hosted publisher sieve chapter](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/07.0_pp_76_107_Principles_and_first_examples_of_sieve_methods.pdf).
  Use the specialization \(x=0,y=U\). Its uniformity in the nonzero
  even shift is explicit; fixed factors are absorbed into an effective
  constant. The preceding sieve construction supplies effectivity.

The original Goldston–Montgomery chapter is *Pair Correlation of Zeros
and Primes in Short Intervals*, Progress in Mathematics 70 (1987),
183–203, [publisher record](https://doi.org/10.1007/978-1-4612-4816-3_10).
Its full text was subscription-only during inspection. BGSTB's remark
points to its Lemma 6, replacing Lemma 7 to avoid an extra logarithmic loss.
We do not claim to have verified the original lemma or import its statement
as a proof dependency. The needed mean-value estimate is proved locally
with explicit sinc kernels. Thus this citation-access gap does not leave
an unchecked analytic input in the local deduction.

Neither imported input is a prime-pair asymptotic, a zero-density
hypothesis, or an RH-conditional correlation theorem. Their upstream
proofs are not fully reconstructed; the source nodes record that scope.

## Local claims and dependencies

| Claim | Manuscript label | Direct inputs |
| --- | --- | --- |
| `PAIR-MEANVALUE-001` | `lem:pair-meanvalue` | Elementary sinc estimates, ordinary \(L^1/L^2\) Fourier inversion and Fubini |
| `PAIR-PRIME-COUNT-001` | `lem:prime-count` | `PRIME-SIEVE-001` |
| `PAIR-PRIME-DIAGONAL-001` | `lem:prime-diagonal` | `PRIME-PNT-001`, elementary proper-power count |
| `PAIR-PRIME-MEAN-001` | `lem:prime-mean` | The preceding three local claims |
| `PAIR-RHS-MEAN-001` | `lem:rhs-mean` | `PAIR-PRIME-MEAN-001`, `PAIR-EF-001` |

The mean-value proof constructs integrable bounds \(M^-\leq1_{[0,T]}
\leq M^+\) by smoothing and correcting at both endpoints.
They have mass \(T\pm512/\delta\), \(L^1\) norm at most \(1025T\),
and Fourier bandwidth \(\delta\). The lower function may be negative;
the sandwich remains valid against the nonnegative function \(|F|^2\).

### Fourier normalization and boundaries

Let \(s(u)=\sin(\pi u)/(\pi u)\), with \(s(0)=1\), and
\(\tau(\xi)=(1-|\xi|)_+\). The transform has negative sign and \(2\pi\)
in the exponential.

| Object | Transform or frequency | Support/boundary |
| --- | --- | --- |
| \(K(u)=\tfrac34s(u/2)^4\) | \(\tfrac32(\tau*\tau)(2\xi)\) | \([-1,1]\); mass 1 |
| \(B_0(u)=s(u/2)^2+s((u-1)/2)^2\) | \(2(1+e^{-2\pi i\xi})\tau(2\xi)\) | \([-1/2,1/2]\); mass 4 |
| \(K_\delta(u)=\delta K(\delta u)\) | \(\widehat K(\xi/\delta)\) | \([-\delta,\delta]\) |
| \(\mathcal P=\sum a_X(n)n^{-it}\) | \(\mu_n=-\log n/(2\pi)\) | Nearby frequencies mean \(0<|\log(n/m)|<2\pi\delta\) |

These are auxiliary Fourier supports, not a support extension for a
correlation test function. \(L^1\) Fourier continuity makes
\(\widehat M^\pm\) zero at both band edges, which justifies the strict
nearby-frequency inequality. Repeated frequencies must be combined
before taking the diagonal. The prime frequencies are distinct.

## Arithmetic and error budget

The shift factor \(g(h)\) has a positive squarefree divisor expansion
whose mean is at most \(V\exp(3/4)\). Odd prime shifts involve the prime 2.
Pairs involving a proper power contribute
\(O(V\sqrt U\log^3(2U))=O(UV)\). These observations prove the averaged
von Mangoldt pair count, including all prime powers.

Dyadic blocks then give \(Q(X,\delta)\ll\delta X\).
The diagonal is \(D(X)=\log X+O(1)\); proper powers contribute
\(O(X^{-1/2}\log^3(2X))=O(1)\).
The exact weight is continuous at \(n=X\), so partial summation introduces
no jump there. Choosing \(\delta=\tfrac12\sqrt{\log(2X)/(TX)}\) gives the
prime-series error \(O(\sqrt{TX\log(2X)})\).

| Error | Bound before final combination |
| --- | --- |
| `E_diagonal` | \(O(T)\), with proper powers retained |
| `E_offdiag` | \(O(\sqrt{TX\log(2X)})\), including the Fourier majorants' diagonal cost |
| `E_archsquare` | \(O(TX^{-2}\log T)\) |
| `E_primearch` | \(O(X^{-1/2}\log(T+2))\), by integration by parts |
| Original remainder norms | \(O(\sqrt T/X)\) for arch and DS, \(O(\sqrt X)\) for pole, \(O(X^{-5/2})\) for trivial zeros |
| `E_remsquare` | \(O(T/X^2+X)\), after bounding each original remainder |

The manuscript separately lists each original remainder's interaction
with \(\mathcal P\) and \(A\), before combining these errors into the
two target scales. In particular the \(\mathcal P/A\) interaction uses
oscillation, not a bound by the product of the two full norms.

## Limits, endpoints, and validation

For fixed \(X\), the prime coefficients are absolutely summable, with
tail \(O(X(\log N+1)/\sqrt N)\) for \(N\geq\max(2,X)\).
This justifies fixed-\(X,T\) integral limits. The Fourier double sum has
absolute majorant \(\|M^\pm\|_1(\sum|c_\mu|)^2\).
The singular-factor and dyadic series use nonnegative convergent
majorants. Partial summation is first finite, then its upper endpoint
tends to infinity with the displayed integrable derivative bound.
All resulting estimates are uniform for \(T\geq3,1\leq X\leq T\);
there is no interchange of asymptotic limits.

The proof includes \(X=1\), \(X=T\), \(T=3\), all prime-power cutoffs,
and empty nearby-pair ranges when their difference cutoff is below 1.
No zero is replaced by a critical-line zero in this part.

Run the existing scripts and `python3 -B scripts/check_pair_prime_mean.py`.
The new script uses exact standard-library rational arithmetic and the
existing Gaussian-rational helper. It compares two independent
piecewise-polynomial descriptions of the Fourier kernel, checks phases,
mass and bandwidth, finite diagonal/prime-power bookkeeping, the divisor
expansion, parameter algebra, and cross-term signs.
Finite coefficient fixtures are marked `SYNTHETIC_MODEL`.
These are regression checks, not proofs of the PNT, sieve, or mean-value
estimates. No numerical certificate or new package is required.

On 2026-09-26, all 38 exact tests passed: 8 for Lemma 1, 11 for Lemma 3,
9 for Lemmas 2/4, and 10 for the prime-side reconstruction.
The 27-claim ledger passed duplicate-key/ID, dependency-resolution and
acyclicity checks, including source-node links. Claim-to-label mapping,
references, citations, local links and Python syntax also passed.
The prime-side dependency closure was checked to contain only
`UNCONDITIONAL` claims and no computer-assisted KV input.
The combined manuscript compiled in an isolated temporary directory using
pdfLaTeX, BibTeX and resolving LaTeX passes to a 22-page PDF, with no
final-pass warnings, unresolved citations/references, or overfull/underfull
boxes. Two overflowing displays found in the first build were reformatted.

The ledger connects `BGSTB-MEAN` to `PAIR-RHS-MEAN-001` and uses
the latter in the full theorem's dependency list. The normalized
asymptotic is now assembled as `PAIR-ASYMPTOTIC-001`; see the
[local theorem and normalization audit](pair-baseline.md#5-local-normalized-theorem--pair-asymptotic-001).
The remaining Work Package A audit and clean-checkout reproducibility
deliverables, journal comparison, and independent review remain pending.
