# Regenerated pair normalization

Task: verification/exposition. Assumptions: `UNCONDITIONAL`.
Claim: `PAIR-ASYMPTOTIC-001`, status `proved-draft`.

Exact arithmetic regenerates the normalization; analytic bounds remain
inputs from the written proof. This is not a proof certificate.

Use `q=log T`, `l=log X`, `a=|alpha|`, `T>=3`, `1<=X<=T`, `a<=1`.
Divide `2 pi Phi` by `T q`, giving `Phi/C_T` with `C_T=T q/(2 pi)`.

| Component | Before division | After division | After X=T^a, l=a*q |
| --- | --- | --- | --- |
| `archimedean_main` | `T * X^(-2) * q^(2)` | `X^(-2) * q` | `q * T^(-2*a)` |
| `prime_main` | `T * l` | `l * q^(-1)` | `a` |
| `E_peak` | `T * X^(-2) * q` | `X^(-2)` | `T^(-2*a)` |
| `E_mean` | `T * q^(1/2)` | `q^(-1/2)` | `q^(-1/2)` |
| `E_compare_T` | `T` | `q^(-1)` | `q^(-1)` |
| `E_compare_X` | `X` | `T^(-1) * X * q^(-1)` | `T^(-1) * q^(-1) * T^a` |

Error rows give absolute scales with unspecified constants.
Comparison signs reverse when solving for `2 pi Phi`; their absolute
bounds do not change. For `3<=T<5` use the direct bounded-height argument.

Absorb the comparison errors using the generated ratios
`T^(-1) * X <= 1` and
`q^(-1/2) <= 1`.

## Final expression

`F_T(alpha) = q * T^(-2*a) + a`
with absolute error `O(T^(-2*a) + q^(-1/2))`.

Negative alpha uses exact evenness. The separate endpoint values are:

| alpha | Main terms | Absolute error scales |
| --- | --- | --- |
| 0 | `q` | `1 + q^(-1/2)` |
| 1 | `T^(-2) * q + 1` | `T^(-2) + q^(-1/2)` |
| -1 | `T^(-2) * q + 1` | `T^(-2) + q^(-1/2)` |

## Scope and sources

- Analytic bounds and uniformity are inputs from the written proof.
- Big-O constants are effective but are not computed here.
- At alpha=0 retain the peak error scale 1, giving total error O(1).
- At alpha=+/-1 the written proof absorbs T^(-2)q into O(q^(-1/2)).
- Full complex-zero weights, multiplicities and C_T are unchanged.
- Published computer-assisted dependencies are not replayed.

Claim IDs and exact manuscript labels for each step are retained in
`pair-normalization.json`. The source proof is `proofs/pair_baseline.tex`.
