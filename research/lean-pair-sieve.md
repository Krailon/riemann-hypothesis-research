# Weighted nearby-prime sieve bound

Assumptions: `UNCONDITIONAL`. Ledger entry: `PAIR-PRIME-COUNT-FORMAL-001`.

## Statements and conventions

The milestone proves both assertions of `PAIR-PRIME-COUNT-001`:

- For real U,V >= 0, the ordered sum of Lambda(m)Lambda(n) over
  1 <= m,n <= U and 0 < |m-n| <= V is at most C_count U V.
- For X >= 1 and 0 <= delta <= 1/2, the existing
  `pairMeanPrimeNearby X delta` is at most C_nearby delta X.

The second sum uses the original coefficients
`Lambda(n)/sqrt(n) * min(n/X,X/n)` and the **strict** logarithmic band
`0 < |log(n/m)| < 2 pi delta`. Index k in the coefficient API denotes
integer k+1. All pairs are ordered. Proper prime powers are retained.
The linear distance cutoff and height cutoff are inclusive. Floors translate
real cutoffs exactly. The linear sum is empty for V<1. X=1, delta=0,
delta=1/2, and exclusion of pairs exactly on the logarithmic boundary are
explicit endpoint declarations.

## Effective constants

Write K=exp(pi). The checked constants are deliberately loose:

    C_prime = 256 (1 + 81 * 16^6 + 512)
    C_power = 128 + 1024/log(2)
    C_count = 2 (C_prime exp(3) + 4 + 2 C_power)
    C_nearby = 32 pi K^3 C_count.

They are independent of U,V,X,delta. No floating-point computation enters
the proof, and no ineffective threshold is hidden in an asymptotic estimate.

## Dependency chain and proof differences

| Modules | Role |
| --- | --- |
| `PairSieveDefinitions` | Definition-only interfaces for the proof and Comparator |
| `PairSieveLocal` | Shifted polynomial n(n+h), residue-negation root equivalence, interval remainder, finite Selberg bound, small-prime exceptions |
| `PairSieveSubset`, `PairSieveLinear` | Finite subset union convolution and marginalization; harmonic lower bound translated from the pinned one-dimensional sieve |
| `PairSieveDenominator`, `PairSieveAverage` | Dimension-two denominator and effective average of the shift factor |
| `PairSieveCutoff` | Explicit eighth-root choice and logarithmic error absorption |
| `PairSievePrimePowers`, `PairSieveShiftCount`, `PairSieveCount` | Proper-power enumeration, odd shifts, ordered-pair regrouping, real cutoffs |
| `PairSieveGeometry`, `PairSieveBall`, `PairSieveCover` | Logarithmic band geometry, actual coefficient envelopes, finite dyadic ball bounds and covering |
| `PairSieveWeighted`, `PairSieveEndpoints` | Absolute double summability, final weighted theorem and endpoints |

The formal proof uses

    G(h) = product_{p|h} (p/(p-1))^2,

including p=2. It proves sum_{1<=h<=V} G(h) <= exp(3) V. The finite
squarefree expansion is bounded using

    ((p/(p-1))^2 - 1)/p <= 3/(p(p-1)),

whose majorant telescopes. There is no infinite Euler-product interchange.
For positive even h, the actual normalizer at primorial(N^2), cutoff N^2,
is at least (log N)^2/G(h). This follows by squaring the harmonic lower
bound, grouping pairs of squarefree subsets by their union, and summing
out primes dividing h. At good primes the convolution weight
`2/(p-1)+1/(p-1)^2` is at most `2/(p-2)`.

This is an alternative sufficient sieve argument. It **does not formalize**
the precise singular factor g(h) in the historical `PRIME-SIEVE-001` source
statement. The original ledger status and source proof remain unchanged.
The even-shift theorem itself is uniform over all positive shifts h,
including h>U; only the first prime is restricted to <=U.

For large U choose N=floor(U^(1/8)); the finite sieve cutoff is N^2.
When log U>=16, log U<=16 log N, and its logarithmic error is absorbed
using log U<=16 U^(1/16). The complementary range is handled directly.
Proper powers in [1,U] use the pinned strict-range enumeration at U+1,
so an endpoint proper power is included. Positive and negative shifts
are related by an exact ordered-pair bijection.

For the weighted step, set R_j=2^j X. A nonnegative majorant B_j is supported
on m,n<=R_j and 0<|m-n|<=2 pi delta R_j, with weight
`8 K^3 X^2/R_j^3 * Lambda(m)Lambda(n)`. Every logarithmically nearby pair
is covered by at least one B_j. Overlap only increases the bound. The
row sums are at most `(C_nearby/2) delta X 2^(-j)`.

All parameters are fixed when summing over j. Each row has finite support;
the geometric bound proves absolute summability of the entire double family.
This justifies reversing the dyadic and pair sums. No limiting relation
between X and delta is imposed.

## Verification

The inventory covers 80 public theorems in 15 modules; 17 statements have
separate definition-only Comparator specifications. Four central imported
inputs are included in the axiom audit: the optimized finite Selberg inequality,
the harmonic lower bound, proper-power enumeration, and residue progression
counting. The only permitted axioms are `propext`, `Quot.sound`, and
`Classical.choice`. An isolated unfinished weighted theorem must be rejected.

Run `python3 scripts/reproduce_lean.py --skip-bootstrap` to build, compare,
audit and archive the milestone with the existing project checks.
The full run passed on 2026-10-16. The content-addressed
[verification manifest](../artifacts/certificates/lean/8f024b266587602508d6e2b9a2533b094b9e667983712d82986c294fcddadbc9/manifest.json)
records 54 commands, all 17 new statement comparisons,
752 total axiom reports, 14 unfinished-proof rejection controls,
24 coverage checks, 70 pair regressions and 126 triple regressions.
Every recorded source, output and tool-binary hash was verified against the
archive. The runner used the existing build cache (`fresh_project_build=false`)
and Lean's default kernel. This is not a fresh-checkout or independent
external-kernel verification claim.

## Remaining work

The subsequent [diagonal milestone](lean-pair-diagonal.md) supplies the
diagonal asymptotic with existential constants, and the
[optimized mean-square milestone](lean-pair-prime-mean.md) assembles
`PAIR-PRIME-MEAN-001` with the same effectivity gap.
The sieve milestone itself supplies no mean-square or correlation asymptotic.
