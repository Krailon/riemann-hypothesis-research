# Finite density counts and conditional window adapters

Assumptions: finite identities are `UNCONDITIONAL`. The four analytic bound
statements require `ZERO_DENSITY(UniformDyadicDensity C T₀)`, defined exactly below.
There is no proved instance of this hypothesis and no new axiom.

## Counts and conventions

Use the existing actual `ZeroOccurrence = Σ ρ : StripZero, Fin (zeroMultiplicity ρ)`.
Every count retains analytic multiplicity, including repeated zeros and equal
ordinates. Write δ=β−1/2. The six finite sets filter either `(a,b]` or `[a,b]`
by δ>D, δ<−D, or |δ|>D. All horizontal thresholds are strict. The cumulative
`rightDensityCount σ V` counts β>σ and 0<γ≤V; its cardinality is proved equal to
the corresponding sum of analytic multiplicities.

`DensityCountIdentities` proves membership, empty intervals, monotonicity,
multiplicity sums, cumulative differences, endpoint corrections, and reflection.
Reflection is the existing multiplicity-preserving map ρ↦1−conj(ρ), with γ fixed
and δ negated. Left and right counts agree for every real D. The two-sided count
is twice the right count **only for D≥0**, when those two strict tails are disjoint.
At D=0, critical-line occurrences are excluded. At |δ|=D, equality is excluded.
Closed singleton windows can have mass; the endpoint identities retain it.

## Explicit analytic hypothesis

`UniformDyadicDensity C T₀ : Prop` has the fields

- C>0 and T₀≥3;
- for every V≥T₀ and 0≤D≤331/1000,
  # {i : V<γᵢ≤2V, δᵢ>D} ≤ C (V^(1−D/4) log V + (log V)²).

This packages the exact uniform statement needed by the adapters, not its proof.
It is neither a typeclass instance nor an imported axiom. In particular, each
analytic bound takes `(h : UniformDyadicDensity C T₀)` as an explicit argument.
The constants below are effective relative to C,T₀; no numerical C,T₀ is certified.

## Checked consequences

For T≥4T₀ the four half-open dyadic windows starting at T/4, T/2, T and 2T
cover the closed interval [T/2,5T/2]. The first window includes γ=T/2;
using only the other three would miss that lower endpoint. Each dyadic count
is at most 4C times T^(1−D/4)log T+(log T)². Summing and reflecting gives

    # {i : T/2≤γᵢ≤5T/2, |δᵢ|>D}
      ≤ 32 C (T^(1−D/4) log T + (log T)²),    0≤D≤331/1000.

Define B_T(v) as this two-sided count with D=v/log T. Then

    B_T(v) ≤ 32 C (T log T exp(−v/4) + (log T)²),
      0≤v≤(331/1000)log T, T≥4T₀.

The scaling identity uses real exponentiation. B_T is antitone for T>1. At and
beyond v=(331/1000)log T it satisfies the frozen bound

    B_T(v) ≤ 32 C (T^(1−331/4000) log T + (log T)²).

All counts are finite; no limit, infinite-sum rearrangement, or integral
interchange is used. The frozen bound is an upper bound by monotonicity, not an
extension of the exponential decay past the stated density range.

## Dependency and source boundary

Lean dependencies: actual strip-zero finiteness, analytic multiplicity and
horizontal reflection; `occurrenceWindow`/`occurrenceInterval`; finite-set
bijections and disjoint unions; real logarithm, exponential and power inequalities.
The solution imports `Zeta23Counting` for existing window identities. It does not
use Riemann–von Mangoldt as a substitute for horizontal zero density.

The historical `ORDINATE-DENSITY-INPUT-001` cites Simonič, Theorem 1 in the
consulted arXiv:1910.08274v2, published in JMAA 491 (2020), 124303. Its uniform
near-line density estimate supplies the intended mathematical input, but the
analytic proof and explicit numerical provenance have not been imported into
Lean. The audited prerequisites include the approximate functional equation,
twisted zeta second moment, Selberg mollifier estimates and Littlewood counting.
Existing imports do not supply this exact finished theorem. The audited Ostmann
density bound has an unsuitable exponent near 1/2; unfinished density declarations
in the PNT dependency cannot be used as proofs.

The GLSS close-pair bound is also a separate missing input; the manuscript route
uses Fujii-type moments of S(t) increments. The checked complex pair statistic
cannot simply replace a nonnegative ordinate close-pair count. Neither a density
moment estimate nor density-based replacement vanishing is asserted here. The
kernel-free signed complex-argument error remains open.

## Reproduction

    python3 scripts/reproduce_lean.py --reuse-dependencies --density-adapters-only

The focused suite is also included in the full harness. It checks 35 public
statements against definition-only Comparator contracts, rejects 11 unfinished
controls (multiplicity, reflection, endpoints, singleton, cumulative differences,
threshold exclusion, doubling, dyadic cover, window bound, scaling and frozen
endpoint), runs the combined project build and complete axiom report, and reruns
coverage, harness, control-pool and pair/triple regressions. Only `propext`,
`Quot.sound` and `Classical.choice` are allowed; Nanoda is not run. Python tests
check bookkeeping and conditional scope, not the mathematics.

The inventory marks the density hypothesis unproved and identifies the four
conditional declarations. Coverage of `ORDINATE-DENSITY-INPUT-001` is partial;
its historical statement and status remain unchanged. Content-addressed run
records and the appended formal implication entry supply the verification record.
