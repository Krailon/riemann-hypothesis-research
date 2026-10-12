# Rational-kernel bounds and exact ordinate transfer

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
This milestone continues the [actual-occurrence construction](lean-actual-occurrences.md).
It proves bounds and fixed-height transfer for the **rationally defined** kernel
in the assembled triple statistic. Its equality with the kernel integral,
horizontal derivatives, and asymptotic estimates are separate obligations.

**Verified:** the fresh-project run on 2026-10-11 UTC passed
**30 new Comparator specifications**, all earlier proof checks, **six
unfinished-proof negative controls**, **202 distinct axiom reports**,
**196 pair/triple regressions**, and **12 coverage-map checks**. The
[complete verification archive](../artifacts/certificates/lean/fa024ffafb1f3c7ba4b83267cfdd48b9ecb55aa2138b00fe6bd01e8e8bc0fadd/manifest.json)
records source hashes, tool pins, logs, and dependency compatibility patches.

The subsequent [integral-profile milestone](lean-integral-profile.md)
identifies this rational profile with its integral and proves horizontal
derivatives and Taylor remainders. Statements below about those remaining
obligations describe the earlier milestone; the current coverage map records
their new checked components. The later [uniform-height milestone](lean-uniform-height.md)
adds global real-test majorants; the signed `o(1)` remains outstanding.

## Rational profile and closed parameter domain

For real gaps a,b and real e,f,g with |e|,|f|,|g| ≤ 1/2, define

\[
c_1=a-ie,\quad c_2=b-if,\quad c_3=ig,\qquad d_{jk}=c_j-c_k,
\]
\[
J=\pi\frac{24+d_{12}^2+d_{13}^2+d_{23}^2}
{(4+d_{12}^2)(4+d_{13}^2)(4+d_{23}^2)}.
\]

`RationalTransferDefinitions.lean` exposes this formula independently of the
solution proofs. For z=x+iy with |y|≤1, Lean proves

\[
\|4+z^2\|\ge3+x^2>0.
\]

Thus all three denominators are nonzero even at coincident centers and the
closed horizontal endpoints. With A,B,C denoting these denominators, the
checked algebraic identity

\[
J=\pi\left(\frac1{AB}+\frac1{AC}+\frac1{BC}+\frac{12}{ABC}\right)
\]

gives the explicit global bound **|J| ≤ 7π/9**, independent of the real gaps
and all horizontal parameters in the cube. No integral evaluation is used.

The proofs also check partner exchange, simultaneous horizontal sign reversal
as complex conjugation, and the real specialization. At coincident centers,
`J(0,0;e,e,−e)=3π/8` for every real e. The fully zero specialization and the
denominator at imaginary endpoint +1 have separate checked statements.

## Actual weighted sums and cutoff limits

An actual tuple is `Fin 3 → ZeroOccurrence`; slot 0 is the anchor. For slots
1 and 2 the gaps in J are **unscaled** ordinate differences. Its horizontal
arguments are respectively δ₁,δ₂,δ₀, with the anchor's positive imaginary sign.
`actualRealKernel` uses the same gaps and sets all three horizontal parameters
to zero. This is a specialization of the kernel, not a replacement of actual
zero occurrences by critical-line zeros.

The existing `actualCorrelationTerm` supplies w(γ₀)F at either real or complex
arguments, keeping the established inverse Fourier convention. The new
`TransferTermKind` names five unnormalized summands:

| Kind | Summand |
| --- | --- |
| `ordinate` | wF(u,v) |
| `weighted` | wJδF(z) |
| `arguments` | wJδ(F(z)−F(u,v)) |
| `horizontal` | w(Jδ−J₀)F(u,v) |
| `gaps` | w(J₀−J*)F(u,v), J*=3π/8 |

All sums include both ordinate signs, full multiplicities, all ordered tuples,
and every diagonal. Fix T, a>0, a complex weight w vanishing outside [T,2T],
and a smooth compactly supported complex Fourier amplitude φ. The previous
milestone proved norm summability of both real and complex test sums and their
difference. Bounded kernel multiplication now gives norm summability of every
row. The horizontal multiplier has norm at most 14π/9 and the gap multiplier
at most 7π/9+|J*|. No positivity of w or symmetry of φ is used.

`rationalTransferTerm_cutoff_limit` removes the three inclusive cutoffs
|γⱼ|≤Nⱼ independently, ordered componentwise on `Fin 3 → ℕ`.
`rationalTransferSum_cutoff_limit` does the same for the normalized sums.
Endpoint membership is inherited from the proved occurrence cutoff interface;
no endpoint occurrence is silently omitted.

## Exact normalization

For T>2π put q=log T, b=log(T/(2π)), ℓ=b/(2π), and c=16/(3Tq).
Both logarithms and ℓ are positive. `rationalTransferSum` multiplies the
ordinate row by 1/(Tℓ) and each other row by c. Thus it defines exactly O,
R, E_arguments, E_horizontal, E_gaps of the transfer manuscript.

Lean verifies the finite-sum telescoping identity and its absolutely summable
infinite version. The normalization calculation is

\[
cJ_* = \frac{b/q}{T\ell},\qquad
R=\frac bq O+E_{\rm arguments}+E_{\rm horizontal}+E_{\rm gaps}.
\]

For any S∈ℂ, it follows that

\[
O-S=\frac qb(R-S-E_{\rm arguments}-E_{\rm horizontal}-E_{\rm gaps})
       +\left(\frac qb-1\right)S.
\]

The benchmark is an arbitrary complex scalar; this algebraic statement does
not require the sine benchmark's analytic construction. The sharper domain
T>2π includes the manuscript's T≥2πe range. The fixed-height identity requires
no hexagonal Fourier-support restriction and proves no limit as T→∞.

`scaledAnchorWeight T ω` is exactly γ↦ω(γ/T). A separate theorem supplies its
support in [T,2T] when ω vanishes outside (1,2), and checks zero values at T
and 2T. The specialized transfer theorem therefore applies to the manuscript's
smooth nonnegative mass-one smoothing, while its proof permits more general
complex weights. Every term and normalized sum vanishes for the zero Fourier
test, also checked separately.

**Limit order:** fix T, scale, weight and test; evaluate the tuple Fourier
integrals; sum absolutely; remove the three cutoffs independently. This result
does not interchange the infinite sum with an unevaluated Fourier integral.

## Verification and remaining work

The [inventory](lean-rational-transfer-inventory.json) lists 30 new public
theorems in three solution modules. Every one has a definition-only Comparator
specification and an explicit axiom report. The solution imports no challenge
module; the intentionally unfinished solution must be rejected for `sorryAx`.
The permitted axioms remain `propext`, `Quot.sound`, and `Classical.choice`,
with the external kernel disabled and the existing dependency pins unchanged.

```bash
python3 -B scripts/reproduce_lean.py --fresh-project
python3 -B scripts/check_lean_analytic_coverage.py
```

The coverage map retains 46 historical nodes and 92 edges, now with 138
component records. The rational transfer and weighted convergence are checked
components of the historical claims. The original integral-profile claim and
its dependent historical claims retain partial coverage. Whole-ledger hash
maintenance does not extend the historical RH audits.

Next prerequisites are the profile's integral evaluation and horizontal
derivative bounds, followed by stronger local counts and uniform height
estimates. The signed complex-argument o(1) remains open research.
