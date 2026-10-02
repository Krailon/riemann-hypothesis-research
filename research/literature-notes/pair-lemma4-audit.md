# Lemmas 2 and 4: counting and height truncation

Task: proof and source verification. Assumptions: `UNCONDITIONAL`.
Status: `proved-draft`; independent review and final journal comparison
are pending. See the [proof](../../proofs/pair_baseline.tex),
[ledger](../theorem-ledger.yaml), and [notation](../notation.md).

## Sources and local claims

The comparison source is BGSTB, [arXiv:2306.04799v1, §2](https://arxiv.org/html/2306.04799v1#S2),
the **PREPRINT version of the published work** (`BGSTB2024`):
Lemma 2, (2.4)–(2.5), and Lemma 4, (2.12)–(2.16).
The intervening definitions (2.9)–(2.11) motivate the horizontal envelope.
No quantitative zero-free region from the subsequent theorem proof is used.

The counting input remains `ZETA-COUNT-001`, the unconditional
[Montgomery–Vaughan Corollary 14.3, p.454](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/18.0_pp_452_462_Zeros.pdf).
The midpoint endpoint definition is on p.452; the adjacent Corollary 14.4
assumes RH and is excluded. These source statements were consulted on
2026-09-25. Their upstream proofs are not reconstructed here.

| Local claim | Proof label | Content |
| --- | --- | --- |
| `PAIR-COUNT-001` | `lem:pair-count` | Inclusive count, full-weight unit intervals, both signs, effective bounded-height bounds |
| `PAIR-COUNT-KERNEL-001` | `lem:count-kernel` | Global, distant, boundary and exterior-integral kernel majorants |
| `PAIR-TRUNC-001` | `lem:pair-trunc` | Exact error decomposition, uniform estimates and the final Lemma 4 comparison |

The dependency chain is
`ZETA-COUNT-001` + `ZETA-ANALYTIC-001` → `PAIR-COUNT-001`
→ `PAIR-COUNT-KERNEL-001`. Truncation additionally uses
`PAIR-EF-CONVERGENCE-001` and `PAIR-NORM-001`.
The Lemma 1 convergence entry now references the local counting claim,
without changing its statement.

## Counting and endpoints

Padded midpoint counts bound the inclusive count and closed unit intervals,
including all endpoint multiplicities. Conjugation covers negative heights.
A short paired alternating-series argument proves that there is no
nontrivial zero with \(\gamma=0\), so the total count is \(2N(V)\).
Bounded-height constants are controlled by the imported count at fixed
heights; the proof does not require a table of low zeros.

The kernel proofs use nonnegative unit-interval and dyadic majorants.
The underlying elementary series estimates, for \(a\geq0\), are
\[
 \sum_{n\geq0}\frac1{1+(a+n)^2}\ll\frac1{1+a},\qquad
 \sum_{n\geq0}\frac{\log(n+2)}{1+(a+n)^2}
 \ll\frac{\log(a+2)}{1+a}.
\]
Their proofs split at \(1+a\) and sum explicit geometric tails.
Every constant is absolute and effective; no decimal optimization is claimed.

## Normalization and horizontal dependence

Use the existing Lemma 3 summands \(v_\rho(t)\) and write
\[
 U_X=\sum_\rho v_\rho,\quad U_{X,Z}=\sum_{|\gamma|\leq Z}v_\rho,\quad
 V_{X,T}=\sum_{0<\gamma\leq T}v_\rho,\quad
 L(X,T)=4\int_0^T|U_X(t)|^2\,dt.
\]
The all-zero sum includes both signs with multiplicity.
Since \(\mathcal S(X,t)=2X^{-it}U_X(t)\), this \(L\) is exactly the
integral of the squared modulus of Lemma 1's zero side.
No Fourier transform or mean-spacing rescaling is used.

Set
\[
 B(Z)=\max(\{0\}\cup\{\delta_\rho:|\gamma|\leq Z\}),\qquad
 \eta_*(Z)=\tfrac12-B(Z).
\]
Finiteness and the open critical strip imply \(0\leq B(Z)<1/2\);
the definition covers an empty finite set. The proof first obtains a bound
with \(X^{2B(Z)}\), then translates it to any **established**
\(B(Z)\leq1/2-\eta(Z)\), with \(0\leq\eta(Z)\leq1/2\).
Neither continuity of \(\eta\) nor a quantitative lower bound is needed
for this lemma. The canonical \(\eta_*\) need not be continuous.

Crucially, \(X^{B(Z)}\) bounds only the retained zero weights.
After extracting that factor, only the nonnegative unweighted kernel
majorants are extended past the cutoff.

## Error and interchange audit

For \(X\geq1,T\geq3,Z\geq2T\), the exact decomposition is
\[
 L=2\pi\Phi+E_{\rm trunc}+E_{\rm height}+E_{\rm extension}.
\]

| Error | Exact definition | Uniform bound |
| --- | --- | --- |
| `E_trunc` | \(4\int_0^T(\lvert U_X\rvert^2-\lvert U_{X,Z}\rvert^2)\,dt\) | \(O(XT[\log(T+2)\log Z/Z+\log^2Z/Z^2])\) |
| `E_height` | \(4\int_0^T(\lvert U_{X,Z}\rvert^2-\lvert V_{X,T}\rvert^2)\,dt\) | \(O(X^{2B(Z)}\log^3T)\) |
| `E_extension` | \(-4\int_{\mathbb R\setminus[0,T]}\lvert V_{X,T}\rvert^2\,dt\) | \(O(X^{2B(Z)}\log^2T)\), and nonpositive |

The first step uses
\(\lvert A\rvert^2-\lvert A-R\rvert^2
=2\Re(A\bar R)-\lvert R\rvert^2\), retaining the quadratic remainder
in the absolute bound. It does not expand an infinite double sum.
The lower/upper boundary kernels contribute
\((1+t)^{-1}+(1+T-t)^{-1}\); integration supplies the third logarithm.
The extension step integrates \((1+a)^{-2}\) outside both endpoints.
All these estimates hold even when \(T\) is exactly a zero ordinate.

Fix \(X,T\) when interpreting the full sum by the previously proved local
uniform convergence. The kernel majorants give absolute integrability on
\([0,T]\); Lemma 3 and the exterior bound control the finite-sum integral
on \(\mathbb R\). The auxiliary \(Z\) is finite throughout.
There is no interchange of two asymptotic limits.

For \(T\geq5\), choose \(Z_*=T\log^2T\). Then \(Z_*\geq2T\),
\(\log Z_*\ll\log T\), and \(E_{\rm trunc}=O(X)\).
For \(3\leq T<5\), that cutoff condition need not hold: instead the proof
bounds \(L\) and \(\Phi\) directly by \(O(X)\), using the global kernel
bound and \(N(5)\). Thus, throughout \(X\geq1,T\geq3\),
\[
 \Phi(X,T)=\frac{L(X,T)}{2\pi}
 +O\bigl(X^{2B(Z_*)}\log^3T\bigr)+O(X).
\]
This is the source's error form after substituting an established envelope.
The proof does not restrict \(X\leq T\), assume simplicity, or discard
horizontal displacements.

## Verification and remaining work

Run from the repository root:

```sh
python3 -B scripts/check_pair_lemma1.py
python3 -B scripts/check_pair_lemma3.py
python3 -B scripts/check_pair_lemma4.py
```

All 28 tests passed on 2026-09-25: 8 for Lemma 1, 11 for Lemma 3,
and 9 new checks for Lemmas 2/4. The new script reuses the existing exact
Gaussian-rational helper and adds no dependencies. It checks midpoint/full
endpoints, occurrence partitions, the signed error decomposition, the
quadratic remainder, phase normalization, horizontal amplitudes and empty
sets, denominator/tail bounds, and the marked `RH` specialization.

Finite fixtures respect reflection, conjugation and multiplicity and are
tagged `SYNTHETIC_MODEL`. The finite weighted error identity is an algebra
check, not numerical quadrature. No computation enters the analytic proof
and no numerical certificate is claimed.

Ledger dependency resolution and acyclicity, theorem-label mapping,
references, citations, local links, TeX delimiter/environment structure,
Python syntax and whitespace checks also passed.

After installation of `booktabs` and `etoolbox`, an isolated build
succeeded on 2026-09-25 using pdfTeX 1.40.25 and BibTeX 0.99d
(TeX Live 2023/Debian). The resulting PDF has 13 pages. All four passes
completed successfully; the final LaTeX pass and BibTeX reported no warnings,
and bibliography entries and cross-references resolved. No mathematical
source changes were needed. Reproduce from `proofs/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error pair_baseline.tex
bibtex pair_baseline
pdflatex -interaction=nonstopmode -halt-on-error pair_baseline.tex
pdflatex -interaction=nonstopmode -halt-on-error pair_baseline.tex
```

Independent review and comparison with the final journal text remain
pending. The [quantitative zero-free-region source](korobov-vinogradov-audit.md)
has now been verified, and `PAIR-ENVELOPE-001` derives
\(B(Z)<1/2-\nu_{\rm KV}(Z)\) for \(Z\geq3\), explicitly covering
\(0<|\gamma|<3\) with a published low-height theorem.
`PAIR-COMPARE-001` now gives the uniform \(O(T)+O(X)\) comparison
for \(T\geq3\), \(1\leq X\leq T\). Its analytic absorption bound is
effective at every height in that range, and it retains the direct
\(3\leq T<5\) argument. The [prime-side mean square](pair-prime-mean-audit.md)
is now reconstructed as `PAIR-RHS-MEAN-001`, and
`PAIR-ASYMPTOTIC-001` assembles the normalized theorem with all
frequency endpoints included. The envelope and comparison claims retain
their external computational dependencies; the Lemmas 2/4 proof above
is unchanged.
