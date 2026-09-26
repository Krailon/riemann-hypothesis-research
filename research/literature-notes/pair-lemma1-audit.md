# Lemma 1 reconstruction audit

Task: proof and source verification. Assumptions: `UNCONDITIONAL`.
The explicitly marked RH specialization in the proof is a check under `RH`.

The conventional proof is [pair_baseline.tex](../../proofs/pair_baseline.tex).
Its four local claims are `proved-draft`, with independent review pending:

| Claim | Proof label | Content |
| --- | --- | --- |
| `PAIR-EF-CONVERGENCE-001` | `lem:ef-convergence` | Absolute/local uniform convergence, inclusive zero counts, and a uniform zero-tail bound. |
| `PAIR-EF-MELLIN-001` | `lem:ef-mellin` | Paired Mellin kernel, including the value zero at its endpoint. |
| `PAIR-EF-EXACT-001` | `prop:ef-exact` | Contour proof, signed residues, exact prime/pole/trivial-zero identity, and continuity at every endpoint. |
| `PAIR-EF-001` | `lem:pair-ef` | BGSTB Lemma 1 with four named uniform remainders. |

The task proves the combined identity directly. It does not assign absolute
convergence to either unpaired Landau series or import the pair asymptotic
as an input. Every zero sum includes both signs of the ordinate and multiplicity.

## Sources actually consulted

All accesses below were on 2026-09-25. `MV2007` denotes Montgomery–Vaughan,
*Multiplicative Number Theory I: Classical Theory*, Cambridge, 2007.
The chapter PDFs are publisher text hosted on Vaughan's website.

- `BGSTB2024`: [arXiv v1, Lemma 1, (2.2)–(2.3)](https://arxiv.org/html/2306.04799v1#S2), the **PREPRINT version of the published work**. Used for the target formula and comparison to its subtraction argument; the final journal text remains unchecked.
- `ZETA-ANALYTIC-001`: DLMF [§25.2(i)](https://dlmf.nist.gov/25.2#i), [Euler product (25.2.11)](https://dlmf.nist.gov/25.2#E11), [functional equation (25.4.2)](https://dlmf.nist.gov/25.4#E2), and [§25.10(i)](https://dlmf.nist.gov/25.10#i). Imports the classical analytic structure. The Euler-series differentiation is justified in the proof.
- `ZETA-COUNT-001`: [MV2007, Chapter 14](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/18.0_pp_452_462_Zeros.pdf), definition on p.452 and Corollary 14.3 on p.454. The source uses half-weight at an endpoint; the proof translates this by sandwiching. The adjacent RH-dependent Corollary 14.4 is excluded.
- `ZETA-CONTOUR-001`: [MV2007, Chapter 12](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/16.0_pp_397_418_Explicit_formulae.pdf), Lemma 12.2 on p.398 and Lemma 12.4 on pp.399–400. Imports the good-height estimate and the left-half-plane bound away from trivial zeros. The statements and their displayed proofs were inspected.
- `GAMMA-DIGAMMA-001`: [MV2007, Appendix C](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/20.3_pp_520_534_The_gamma_function.pdf), Theorem C.1, (C.17), and its Euler–Maclaurin proof, pp.523–524. Used only in a fixed sector containing \(3/2-it\).

These published inputs are trusted classical results with their hypotheses
checked at use; their entire upstream proofs have not been reconstructed.
The ledger therefore keeps `dependency_graph_complete: false` where these
inputs occur and distinguishes source verification from independent checking.

## Limit and error audit

| Operation | Justification recorded in the proof |
| --- | --- |
| Infinite zero sum | Denominator bounded below by \(3(1+(t-\gamma)^2)/4\); dyadic counting bounds give an absolute tail. |
| Euler series inside the right contour | Product of a convergent \(\sum\Lambda(n)n^{-5/2}\) and an integrable rational kernel; Fubini applies. |
| Removing horizontal sides | First fix \(X>1,t,M\), then take good heights \(U_j\to\infty\); error \(O_{X,t,M}(\log^2 U_j/U_j^2)\). |
| Moving the left side | Next take \(a=2M+1\to\infty\); bound \(O(X^{-a-1/2}\log(a+\lvert t\rvert+2)/a)\). |
| Trivial-zero residue sum | Uniform termwise majorant \(2/m^2\). |
| Extending to \(X=1\) | Finally use local uniform convergence/dominated convergence of the combined identity. |
| Prime-power endpoints | The intermediate coefficient \(X/n-n/X\) vanishes at \(n=X\); the final prime weight is exactly one. |

Only after the exact identity is established are the uniform remainders bounded:
`E_arch` and `E_DS` are each \(O(X^{-1})\),
\(\lvert E_{\rm pole}\rvert\leq4X^{1/2}/(1+t^2)\), and
\(\lvert E_{\rm trivial}\rvert\leq12X^{-5/2}/(\lvert t\rvert+2)\).
Constants are effective; no optimized decimal constant is asserted.

## Verification and remaining gates

Run the dependency-free exact rational regression checks with:

```bash
python3 scripts/check_pair_lemma1.py
```

They cover residue signs, paired resolvents, prime recombination, endpoint
weights, denominator bounds, and algebra at zero horizontal displacement.
They use no floating point, randomness, or zero dataset. They are finite
regression checks, not a proof of the contour limits or an interval certificate.
No computation is used in the mathematical proof.

On 2026-09-25, all eight regression tests passed. Six supplementary symbolic
kernel/residue identities simplified exactly to zero using the environment's
SymPy 1.12. Ledger dependency resolution and acyclicity, theorem-label mapping,
citations, local links, and TeX delimiter/environment checks also passed.
SymPy is not required by the committed regression script.

For a TeX-equipped checkout, compile from `proofs/`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error pair_baseline.tex
```

After installation of the missing TeX packages, the combined draft compiled
successfully on 2026-09-25: 13 pages, with bibliography and references resolved
and no final-pass warnings. See the [build record](pair-lemma4-audit.md).
Independent mathematical review and journal-version comparison remain pending.
Current reconstruction status is in the [baseline note](pair-baseline.md).
