# Project notation

Task type: exposition. Assumptions: `UNCONDITIONAL`.
These conventions implement AGENTS.md §2; they assert no correlation theorem.

- A nontrivial zero is \(\rho=\beta+i\gamma\), with
  \(\delta_\rho=\beta-1/2\). Zeros are counted with multiplicity.
- The symmetries are \(\rho\mapsto1-\rho\) and
  \(\rho\mapsto\bar\rho\). Their composition
  \(\rho\mapsto1-\bar\rho\) preserves a positive ordinate and multiplicity.
- For \(T>2\pi\), use
  \(L_T=\log(T/2\pi)/(2\pi)\),
  \(u_{jk}=L_T(\gamma_k-\gamma_j)\), and
  \(x_\rho=(\beta-1/2)\log T\).
- The Fourier convention is
  \[
  \widehat f(\xi)=\int_{\mathbb R}f(u)e^{-2\pi i u\xi}\,du,
  \qquad f(u)=\int_{\mathbb R}\widehat f(\xi)e^{2\pi i u\xi}\,d\xi,
  \]
  with the dot product in higher dimensions and hypotheses specified at use.
- \(I_T\) indexes all zero occurrences with \(0<\gamma\leq T\);
  \(N(T)=|I_T|\). Distinct indices can represent the same complex zero.
  \(\mathcal Z_T\) is the set of distinct complex zeros in that range;
  \(m(z)\) is the multiplicity of \(z\in\mathcal Z_T\).
- Every tuple sum specifies its index set. The conditions \(j=k\),
  \(\rho_j=\rho_k\), and \(\gamma_j=\gamma_k\) are different diagonal
  conventions; none is implicit in a distinctness assertion.
- For the pair baseline only, set
  \(A_T=\log T/(2\pi)\), \(C_T=TA_T\), and
  \(q_T=A_T/L_T\). Keep \(C_T\), \(TL_T\), and \(N(T)\) distinct.
  Use \(X>0\) for the source's exponential base to avoid conflict with
  \(x_\rho\); use \(\Phi(X,T)\) and \(\mathcal F_T(\alpha)\) for its
  unnormalized and normalized pair sums.

The imported pair theorem permits \(T\geq3\). Translations involving
\(L_T^{-1}\) in this project use \(T>2\pi\).

## Machine-checkable pair conventions

The [convention and support table](pair-conventions.json) records these
definitions and their exact translations, with stable record IDs, domains,
source claims and source labels. It also records the separate auxiliary
Fourier bandwidth and kernel supports used in the prime-side proof.
The theorem's closed frequency interval and the strict nearby-frequency
cutoff are different records; a closed support interval can have zero
transform values at both endpoints.

Run the [exact checker](../scripts/check_pair_conventions.py) with:

```bash
python3 -B scripts/check_pair_conventions.py
```

It also runs under the existing discovery command:

```bash
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py' -v
```

The table is JSON with schema version 1. Each record has an `id`,
`kind` and `source` (claim ID, file, label); non-domain records
also name their applicable `domain`. Definition records are ordered
and can refer to earlier definitions. Identities give `left` and
`right` expressions. Domain conditions use explicit comparison
operators; intervals record bounds, endpoint inclusion, their role,
and whether the transforms vanish at the endpoints. Requirement records
retain the compactly supported smooth test-function condition.

The checker reads these fields, using only integer literals, named symbols,
unary signs, and `+ - * /` in formulas; for example `1/2`
is exact. Calls, attributes, powers, floating-point values and unknown
symbols are rejected. The formal symbols `p`, `ell`,
`c` and `ell_X` denote \(2\pi,\log T,\log(2\pi)\) and
\(\log(2X)\). Rational fixtures exercise identities subject to
\(\log(T/(2\pi))=\ell-c\); they are not numerical approximations to
those constants or logarithms. In particular the checker compares
exponents and does not approximate exponential functions.

The tests check algebra, recorded domains and boundary conventions,
and reject deliberate mutations. The analytic validity and uniformity
of the underlying estimates still rest on the cited written proofs.
Source validation checks stable claim IDs in the ledger and local
manuscript labels or Markdown headings; it is not a full YAML-ledger
schema validator or an independent source review. No new theorem or
numerical certificate is asserted.
