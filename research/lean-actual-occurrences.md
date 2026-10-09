# Actual zero occurrences and fixed-height convergence

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
This milestone instantiates the [summability foundations](lean-summability.md)
with actual zeta zeros. It supplies fixed-height absolute convergence and
cutoff removal for the real and complex Fourier-test sums and their difference.
The rational kernels, sharp local zero counts, uniform height asymptotics,
and the remaining signed `o(1)` are separate obligations.

**Verified:** the fresh-project run on 2026-10-09 UTC passed **48 new
Comparator declarations**, all earlier proof checks, five unfinished-proof
negative controls, **172 distinct axiom reports**, **196 pair/triple
regressions**, and **10 coverage-map checks**. The
[complete verification archive](../artifacts/certificates/lean/4baad1a05cee7651be493818f37f1effaea8900b0b8ed21aa961bf84929bd28a/manifest.json)
records source hashes, tool pins, logs, and dependency compatibility patches.

## Occurrences, multiplicity, and endpoints

`StripZero` is the subtype of complex numbers satisfying
`riemannZeta ρ = 0` and `0 < ρ.re < 1`. Define

\[
m(\rho)=\operatorname{analyticOrderNatAt}(\zeta,\rho),\qquad
I=\coprod_{\rho\in\mathrm{StripZero}}\mathrm{Fin}(m(\rho)).
\]

The proof establishes analyticity, finite analytic order, positivity of the
order, and equality with the imported integer meromorphic order before using
this interpretation. In particular, the conversion of infinite order to the
natural-order junk value zero is excluded. Each complex zero has exactly
`m(ρ)` occurrences; all ordered occurrence tuples retain coincidences.

The cutoff is inclusive: `occurrenceCutoff U = {i : |γ_i| ≤ U}`. It is finite
for every real U, empty for U < 0, and contains every endpoint occurrence.
Integer cutoffs exhaust I; I is countable and every ordinate fiber is finite.
The proof includes both ordinate signs and any real-axis bucket. It does not
need a separate theorem excluding real strip zeros.

Conjugation preserves order by the pinned library lemma. For `ρ ↦ 1−ρ`, the
functional equation expresses the reflected zeta function locally as an
analytic factor times zeta. Orders therefore satisfy one inequality; applying
the same argument at the reflected point gives the reverse inequality. Their
composition yields an occurrence involution for `ρ ↦ 1−conj(ρ)`, carrying the
multiplicity index unchanged, preserving γ and negating δ = β−1/2.

The definition-only interface uses conditional definitions for finite cutoffs
and the occurrence reflection. The solution proves that their fallback branches
are unreachable. Those definitions allow the Comparator specifications to
refer to the actual objects without importing this milestone's proofs.

## Counting and actual shells

The imported theorem
`Backlund.zetaSurrogate_zeros_in_closedBall₀_count` bounds the divisor mass
of the entire surrogate of `(s−1)ζ(s)` by `C'(1+R)^(3/2)` for R ≥ 1.
The surrogate is patched to have value one at the pole, so the pole's
point-value convention creates no spurious zero. The local divisor/order
bridge is reproduced from the source's private argument.

Every strip zero with |γ| ≤ U has norm at most U+1. Its full positive order
contributes to the surrogate divisor mass. It is never the origin, which the
source's ball-mass definition excludes. Enlarging the exponent proves

\[
\#\{i\in I:|\gamma_i|\le U\}\le C(1+U)^2\quad(U\ge0).
\]

Fix T and a > 0. For anchor occurrences with γ₁ ∈ [T,2T], put

\[
r=\max(|a(\gamma_2-\gamma_1)|,|a(\gamma_3-\gamma_1)|).
\]

`dyadicIndex` partitions these anchored triples into the exact shells
`2^n ≤ 1+r < 2^(n+1)`. Each partner in shell n has
`|γ| ≤ U_n = 2|T| + 2^(n+1)/a`. Write A_T for the finite number of anchor
occurrences and K = 1+2|T|+2/a. The two partner counts give

\[
\#D_n\le A_T C^2 K^4 2^{4n}.
\]

The actual shell construction, cardinality bound, and lower radius bound feed
the existing abstract summability theorem. No counting hypothesis remains in
the resulting actual-zero convergence statements. This qualitative polynomial
bound does not formalize the sharper `PAIR-COUNT-001` or the uniform estimates
of `ORDINATE-COUNT-001`.

## Fourier convention and bounded imaginary strips

For any smooth compactly supported complex amplitude φ on ℝ², the definition is

\[
F_\phi(z_1,z_2)=\int_{\mathbb R^2}\phi(\xi,\eta)
 e^{2\pi i(z_1\xi+z_2\eta)}\,d\xi\,d\eta.
\]

Each integral is integrable. For z = x−iy the twisted amplitude is
`φ(ξ) exp(2π y·ξ)`, with the **positive** sign in this real exponential.
Lean identifies the integral exactly with the inverse Fourier transform of
that amplitude. The internal Euclidean space is `WithLp 2 (ℝ × ℝ)`;
mathlib's measure-preserving coordinate equivalence justifies returning to
product Lebesgue measure without a normalization factor.

The auxiliary compact-family theorem proves continuity of parameterized
iterated derivatives and bounds their L¹ norms on a common compact support.
Mathlib's Fourier derivative estimate then gives uniform rapid decay. For
each B ≥ 0 and natural n there is C > 0 such that

\[
|F_\phi(x-iy)|\le C(1+\max(|x_1|,|x_2|))^{-n},\qquad |y_j|\le B.
\]

The bound includes the coordinate axes, origin, and zero imaginary band.
No symmetry, positivity, tensor-product restriction, or Fourier-support
polytope restriction is needed for this convergence theorem.

## Assembled statements and limit order

`actualCorrelationTerm a w φ b` sums over all `Fin 3 → ZeroOccurrence`, with
anchor weight w(γ₁). The weight can be any complex function vanishing outside
[T,2T]: its values on the finite anchor set are automatically bounded.
For the manuscript's smooth anchor use `w(γ) = ω(γ/T)`.

The Boolean b selects real arguments or

\[
\bigl(a(\gamma_2-\gamma_1)-ia(\delta_2+\delta_1),\;
      a(\gamma_3-\gamma_1)-ia(\delta_3+\delta_1)\bigr).
\]

The unconditional strip bounds give |δ| < 1/2, so both imaginary displacements
are bounded by a at fixed scale. Fourier decay and the actual shell counts
prove norm summability for both choices and for their difference.
`project_actual_summable_norm` specializes a to the exact project mean spacing
`log(T/(2π))/(2π)` for T > 2π.

For every p > 4, the anchored tail is bounded by
`K₀ θ^N/(1−θ)`, where `θ = 2^4/2^p`. In particular the previously checked
ratios for p = 20 and 22 apply. Constants depend on the fixed height, scale,
weight, amplitude, and derivative order; no uniform height estimate is claimed.

Independent inclusive cutoffs are indexed by `Fin 3 → ℕ` with componentwise
order. Their sums converge to the full sums. Actual ordinate regrouping,
five-pattern decomposition, and eight-reflection identities follow, including
the eight-reflection identity for the signed difference. Reflection preserves
both height cutoffs and every ordinate-equality pattern.

**Order of operations:** fix height and tests; evaluate each tuple's Fourier
integral; sum absolutely; remove the three cutoffs independently. A subsequent
height limit requires additional bounds. Summability of evaluated integrals
does not authorize interchanging the zero sum with the unevaluated integral.

## Provenance and verification

The [inventory](lean-actual-occurrences-inventory.json) contains 57 public
project declarations: 48 have separate definition-only Comparator
specifications and nine supporting lemmas have kernel-build and axiom-report
coverage. The latter are the meromorphic-order and divisor-mass bridges,
two shell implementation lemmas, and four general Fourier-family lemmas.
Private helpers are checked transitively by Lean. The new challenge has an
unfinished-proof negative control.

Pinned inputs:

- `PrimeNumberTheoremAnd` at `c39a751132c88b6e8080b74c74023fd95b3d8be0`,
  `Backlund/ZeroCountCrude.lean` and `IEANTN/KadiriZeroCounting.lean`:
  entire-surrogate mass bound, finite positive zero order, and conjugation
  invariance. The separate Riemann–von Mangoldt hypothesis appearing in other
  portions of the latter file is not an assumption of the imported lemmas.
- mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`:
  analytic orders, Schwartz/Fourier derivative estimates, Haar measure
  conversion, and summability/reindexing infrastructure.
- These are resolved through the existing OpenAI checkout at
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The new proof modules do not import
  the quasi-RH theorem and use only the ordinary open critical strip.

The four selected external inputs also have explicit axiom reports. All
accepted proofs are restricted to `propext`, `Classical.choice`, and
`Quot.sound`. The external kernel remains disabled. Exact pins, compatibility
patches, source hashes, and logs are archived by the reproduction harness.

```bash
python3 -B scripts/reproduce_lean.py --fresh-project
python3 -B scripts/check_lean_analytic_coverage.py
```

The coverage map continues to have 46 historical nodes and 92 edges, with
108 component records across this milestone and its summability predecessor.
The full transfer and counting claims retain partial coverage. Next work is
the actual rational-kernel estimates and exact transfer normalization, followed
by the stronger local counts and uniform height estimates required by the
analytic dependency graph. The signed `o(1)` remains open research.
