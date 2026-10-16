# Fourier mean-value input and prime-series specialization

Assumptions: `UNCONDITIONAL`. Ledger: `PAIR-MEANVALUE-FORMAL-001`.

## Checked statement

For a countable index type, injective real frequencies μ, and complex
coefficients with Σ |cᵢ| finite, let

- F(t) = Σ cᵢ exp(2πi μᵢt);
- D = Σ |cᵢ|²;
- Qδ = Σ_{i,j: 0<|μᵢ−μⱼ|<δ} |cᵢ| |cⱼ|.

`pairMeanValue_explicit` proves, for T≥1 and 1/(2T)≤δ≤1/2,

    |∫₀ᵀ |F(t)|² dt − TD| ≤ 512 D/δ + 1025 T Qδ.

Q counts **ordered pairs**, with a strict frequency cutoff. Injectivity
prevents uncombined repeated frequencies from being mistaken for the diagonal.
No minimum separation hypothesis is used.

## Proof dependencies and conventions

| Modules | Checked content |
| --- | --- |
| `PairMeanDefinitions`, `PairMeanSeries` | Cycles convention, norm-one characters, absolutely summable product majorants, continuity |
| `PairMeanKernelBounds`, `PairMeanBoundaryLower` | Continuous sinc at zero, integrable K and B, lower bound including removable points |
| `PairMeanFourier`, `PairMeanTriangle`, `PairMeanFourierRules` | Negative-sign Fourier transform, box convolution, inversion, scaling and translation |
| `PairMeanKernelTransforms`, `PairMeanKernelMass`, `PairMeanKernelTail` | K̂=(3/2)(τ*τ)(2ξ), B̂=2(1+e(−ξ))τ(2ξ), masses 1 and 4, H(|u|)≤64B(u) |
| `PairMeanEnvelope`, `PairMeanSandwich` | M⁻≤1_[0,T]≤M⁺ pointwise; masses T±512/δ; L1≤T+512/δ; vanishing for |ξ|≥δ |
| `PairMeanIntegration`, `PairMeanOffDiagonal` | Absolutely convergent weighted double series, exact diagonal, strict-band nearby-pair bound |
| `PairMeanValue` | Explicit mean-value theorem |
| `PairMeanPrimeDefinitions`, `PairMeanPrimeBridge`, `PairMeanEndpoints` | Actual prime series, coefficient and cutoff translation, empty/singleton and parameter endpoints |

Here s(u)=sinc(πu), K(u)=(3/4)s(u/2)^4,
B(u)=s(u/2)^2+s((u−1)/2)^2, and τ(ξ)=max(0,1−|ξ|).
The Fourier transform uses exp(−2πitξ). Its support endpoint values vanish
by the explicit formulas, so the strict cutoff needs no limiting convention.
The interval indicator uses closed endpoints; Lebesgue integration agrees
with the usual oriented integral when T≥1.

All sum/integral interchanges use absolute integrability. The weighted
product-series majorant is |M(t)|(Σ |cᵢ|)^2. Fourier inversion is applied
to integrable continuous triangles/convolutions with integrable transforms.
All parameters are fixed during each interchange; the resulting constants
are uniform. There are no floating-point proof steps.

## Actual prime-series bridge

Index n denotes the integer n+1. Lean proves the exact coefficient identity

    a_X(n+1) = Λ(n+1)/sqrt(n+1) * min((n+1)/X, X/(n+1)),

its nonnegativity and absolute summability for X≥1, injectivity of
μₙ=−log(n+1)/(2π), and P(X,t)=Σ a_X(n+1)e(μₙt).
The nearby-pair condition is exactly

    n ≠ m and |log((n+1)/(m+1))| < 2πδ.

`pairMeanPrime_meanvalue` specializes the explicit bound to the actual P.
X=1, T=1, both allowed δ endpoints, empty and singleton frequency sets,
and Λ(1)=0 are covered.

## Verification

The inventory lists 106 public declarations. The definition-only Comparator
checks 27 selected statements, including the theorem and prime specialization.
An isolated unfinished solution must be rejected for `sorryAx`.
All public declarations and three central imported Fourier/integration inputs
have axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. Solution modules contain no unfinished proofs.

Run `python3 scripts/reproduce_lean.py --skip-bootstrap` to reproduce the
project checks and archive the result.

The full runner passed on 2026-10-15. The content-addressed
[verification manifest](../artifacts/certificates/lean/3c88062a80f8a70e58f738feb8289eab62898fb987238eca527b13b67b874c68/manifest.json)
records all 27 new statement comparisons, 668 total axiom reports,
13 unfinished-proof rejection controls, 22 coverage checks, 70 pair
regressions and 126 triple regressions. Every archived source and output
hash was verified. This run used the existing project cache
(`fresh_project_build=false`) and Lean's default kernel; it does not claim
fresh-checkout or independent external-kernel verification.

## Remaining arithmetic

The [weighted nearby-prime bound](lean-pair-sieve.md) is now checked.
Next formalize `PAIR-PRIME-DIAGONAL-001`,
including proper prime powers, and optimize δ to recover
`PAIR-PRIME-MEAN-001`. The RHS mean square, pair asymptotic, and triple theorem
are not promoted by this Fourier foundation. Historical ledger blocks and
baseline audit scope are preserved.
