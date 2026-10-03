# Conrey--Snaith: sine benchmark conventions

Task: source audit and exposition. Assumptions: `UNCONDITIONAL` for the
finite unitary identity and the deterministic identities used here.
No zeta correlation theorem is imported.

## Source and consulted version

J. B. Conrey and N. C. Snaith, *In support of n-correlation*,
Communications in Mathematical Physics **330** (2), 639--653 (2014),
[DOI 10.1007/s00220-014-1969-1](https://doi.org/10.1007/s00220-014-1969-1).
Bibliography key: `ConreySnaith2014` in [literature.bib](../literature.bib).

Full text inspected on 2026-10-02:
[author-hosted manuscript](https://people.maths.bris.ac.uk/~mancs/papers2/in_support_arxiv.pdf),
marked **arXiv:1212.5537v2, 2 September 2013**;
[arXiv record](https://arxiv.org/abs/1212.5537).
Published metadata was checked against the
[Bristol record](https://research-information.bris.ac.uk/en/publications/in-support-of-n-correlation/).
The full text consulted is the author manuscript; no final-journal-text
comparison is claimed or required for the direct proof here.

## Exact use

**Theorem 1, equation (2), manuscript p. 2** gives the finite Haar-unitary
identity for a starred sum over ordered distinct eigenvalue indices,
with measure `(2pi)^(-n) d alpha` and determinant of
`S_N(alpha)=sin(N alpha/2)/sin(alpha/2)`.
The elementary limit `S_N(2pi x/N)/N -> sin(pi x)/(pi x)` fixes the
unit-density sine-kernel convention. This is the sole external benchmark
input; the project proves its three-level determinant expansion, the
five occurrence partitions, and every Fourier identity directly.

**Theorem 2, equations (7)--(9), manuscript pp. 4--5** uses a
negative-exponential Fourier representation and three-frequency support
`sum |lambda_j| < 2-epsilon`. We use this only as a convention comparison:
for `F(x2-x1,x3-x1)` the project positive-inverse vector is
`(-xi-eta,xi,eta)`; in the source representation it is
`(xi+eta,-xi,-eta)`. Its absolute sum is `2h`. Project support
`h<=1-kappa` lies strictly inside the source open region with any fixed
`0<epsilon<2kappa`; equality of the numerical boundary values alone
would not change the source's strict inequality.
**No zeta theorem, hypotheses, proof step, or error term from Theorem 2
is imported.**

## Project claims and scope

- `TRIPLE-SINE-MEASURE-001` is an unconditional deterministic tempered
  distribution identity, proved without an external analytic dependency.
- `TRIPLE-MAIN-TERM-COMPARISON-001` combines it with the project's existing
  signed-test and kernel-localization results. The result retains full
  complex zeros and all occurrence-index patterns.

See the [comparison and convention table](../triple-main-term-comparison.md).
The normalization is `A[phi]=(3/2) S_3[F]`; the finite-height local
critical-line factor remains `3 log(T/(2pi))/(2 log T)`. Ordinary-cumulant
cancellation refers only to the benchmark. Neither RH nor simplicity of
zeta zeros is assumed.
