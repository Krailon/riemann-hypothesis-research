# Lemma 3: squared norm, contours and multiplicity

Task: proof and source verification. Assumptions: `UNCONDITIONAL`.
Status: `proved-draft`; independent mathematical review is pending.
The [proof](../../proofs/pair_baseline.tex) uses the
[project conventions](../notation.md) and records claims in the
[theorem ledger](../theorem-ledger.yaml).

## Source and scope

Reconstruction of BGSTB, [arXiv:2306.04799v1](https://arxiv.org/pdf/2306.04799v1),
Lemma 3, equations (2.6)–(2.8), using reflection (2.1).
Bibliography key: `BGSTB2024`. This is the **PREPRINT version of the
published work**; comparison with the final journal text is pending.
The squared-norm statement is proved locally, rather than used as an
imported dependency. The full pair-correlation asymptotic remains imported.

| Local claim | Proof label | Content |
| --- | --- | --- |
| `PAIR-NORM-INTEGRAL-001` | `lem:norm-integral` | Rational integral with complex shift, including coincident poles |
| `PAIR-NORM-001` | `lem:pair-norm` | Squared norm, explicit tail, reflection of the full occurrence sum |
| `PAIR-POSITIVITY-001` | `cor:pair-positivity` | Reality, nonnegativity and inversion/evenness |

For fixed \(X>0,T\geq3\), let \(I_T\) include every occurrence of
\(\rho_j=1/2+\delta_j+i\gamma_j\) with \(0<\gamma_j\leq T\).
Multiplicity and the upper height endpoint have full weight. This finite
set differs from the infinite, both-sign zero sum in Lemma 1.
All ordered pairs are included. With positive-real powers interpreted
using \(\log X\), put
\[
 V_{X,T}(t)=\sum_{j\in I_T}
 \frac{X^{\delta_j+i\gamma_j}}{1+((t-\gamma_j)+i\delta_j)^2}.
\]
Then
\[
 \sum_{j,k\in I_T}\frac{4X^{\rho_j-\rho_k}}{4-(\rho_j-\rho_k)^2}
 =\frac2\pi\int_{\mathbb R}|V_{X,T}(t)|^2\,dt.
\]
This includes \(X=1\), \(0<X<1\), and an empty \(I_T\).

## Convergence and contour audit

1. **Absolute integrability.** For
   \(M_X=\max(X^{1/2},X^{-1/2})\), each summand has modulus at most
   \(4M_X/[3(1+(t-\gamma_j)^2)]\). It lies in \(L^2\); each pair
   product lies in \(L^1\) by Cauchy–Schwarz. The squared-modulus
   expansion is finite, so termwise integration needs no infinite-sum
   theorem. For \(R\geq2(T+1)\), the integral tail is at most
   \(512M_X^2N(T)^2/(27R^3)\). Parameter dependence is explicit.
2. **Elementary integral.** For \(\lvert\Im a\rvert<1\),
   \(J(a)=\int_{\mathbb R}[(1+u^2)(1+(u+a)^2)]^{-1}du
   =2\pi/(4+a^2)\). An upper semicircle of radius
   \(R\geq4(|a|+1)\) contributes at most \(16\pi/R^3\).
   When \(a\ne0\), the two simple upper residues give the formula.
   When \(a=0\), an explicit antiderivative gives \(J(0)=\pi/2\);
   no division by \(a\) is used at coincident poles.
3. **Off-line shift.** Write \(d=\gamma_j-\gamma_k\),
   \(h=\delta_j+\delta_k\), \(a=d-ih\), and
   \(u=t-\gamma_j+i\delta_j\). The second denominator is
   \(1+(u+a)^2\). The four pole heights are \(1,-1,h+1,h-1\).
   None lies in the closed strip between heights \(0\) and \(\delta_j\),
   since \(|\delta_j|,|\delta_k|<1/2\). The joining sides contribute
   at most \(16/R^4\) for \(R\geq4(|a|+1)\).
4. **Order of limits.** Hold \(X,T,j,k\) fixed while removing contours.
   Only a finite pair sum follows. There is no \(T\to\infty\) limit,
   infinite zero-sum exchange, or implicit uniform asymptotic.

## Reflection, diagonals and RH audit

The pair integral yields the rational weight at
\(\rho_j+\bar\rho_k-1=h+id\), with coefficient \(2\pi\).
Multiplying by \(2/\pi\) gives the required coefficient 4.
The map \(\rho_k\mapsto1-\bar\rho_k\) permutes \(I_T\), including
multiplicity and zeros at \(\gamma=T\). Reindexing the complete sum
therefore recovers the original weight at \(\rho_j-\rho_k\).

The original index diagonal contributes \(N(T)\). Before reflection,
the norm expansion's index diagonal contributes
\(\sum_j X^{2\delta_j}/(1-\delta_j^2)\), generally a different value.
The reindexing does not preserve diagonal subsets. Also, \(a=0\) can
occur for distinct reflected off-line zeros at the same ordinate.

The only imported zeta input is `ZETA-ANALYTIC-001`: strip location,
discreteness and multiplicity-preserving functional-equation/conjugation
symmetry. Quantitative zero counts, zero-density estimates, prime estimates,
RH and simplicity are not used. The manuscript's explicitly marked `RH`
specialization removes the line shift and recovers \(4/(4+d^2)\).
Positivity follows from the full squared norm. Inversion follows by
exchanging the two indices and using the even rational weight, so
\(\mathcal F_T\) is even for all real arguments without using an asymptotic.

## Reproduction and remaining review

Run from the repository root:

```sh
python3 scripts/check_pair_lemma1.py
python3 scripts/check_pair_lemma3.py
```

On 2026-09-25, all 8 existing Lemma 1 tests and all 11 Lemma 3 tests passed.
The new tests use only standard-library exact Gaussian rational arithmetic
and formal vertical phases. They check residues and normalization, the
coincident case, contour-pole separation, substitution signs, reflection,
conjugation, inversion, multiplicity, height endpoints and the marked RH
specialization. Symmetric finite fixtures are tagged `SYNTHETIC_MODEL`;
they are algebra regression inputs, not proposed zeta data. No computation
is used in the analytic proof and no numerical certificate is claimed.
Ledger dependency resolution and acyclicity, theorem labels, references,
citations, local links, TeX delimiter/environment structure, Python syntax
and whitespace checks also passed. These static checks do not compile TeX.

The environment has no `latexmk`, `pdflatex` or `tectonic`; PDF compilation
has not been performed. When a TeX toolchain is available, run
`latexmk -pdf pair_baseline.tex` from `proofs/`.
Independent mathematical review and final journal comparison remain pending.
The next bounded reconstruction is Lemma 4, with the needed Lemma 2
counting bounds and its separate uniform truncation errors.
