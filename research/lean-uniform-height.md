# Local zero counts and uniform height estimates

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
This continues the [integral-profile milestone](lean-integral-profile.md).

**Verified:** the fresh-project run on 2026-10-12 UTC passed
**65 new Comparator specifications**, all earlier proof checks, **eight
unfinished-proof negative controls**, **362 distinct axiom reports**,
**196 pair/triple regressions**, and **16 coverage-map checks**. The
[complete verification archive](../artifacts/certificates/lean/440c7011ea2b1baa1b2f526b6d50b089d800dd460772ed22e4c34298af72ee9e/manifest.json)
records source hashes, tool pins, logs and dependency compatibility patches.

## Scope and conventions

All sums use actual `ZeroOccurrence` indices. Each nontrivial zero occurs
according to its analytic multiplicity; both signs of the ordinate are allowed.
Closed interval counts include both endpoints. All triple sums are ordered,
include every diagonal and partial diagonal, and anchor the first occurrence in
**[T,2T]**. No simplicity or RH premise is present.

Write q=log T, ell=log(T/(2 pi))/(2 pi), and
T0=2 pi exp(2 pi). The height estimates hold for every T>=T0, including T0.
Then T>=3, q>=1 and ell>=1. The unscaled ordinate kernel is
kappa(x)=1/(1+x^2). The triple radius is
r=max(|ell(gamma2-gamma1)|,|ell(gamma3-gamma1)|).
The more general scale-a theorems hold uniformly for every a>=1.

Constants are absolute existential constants unless a derivative order or
natural decay exponent is displayed. They are not supplied as numerically
effective constants: the low-height bucket uses the finite count at height 5.
No floating point computation enters these proofs.

## Checked claims

| New ledger ID | Exact scope | Main Lean declaration |
|---|---|---|
| `LOCAL-ZERO-COUNT-001` | Closed unit interval O(log(|v|+2)); general closed interval; inclusive cumulative O((U+1)log(U+2)) | `occurrence_count_local`, `occurrence_count_interval`, `occurrence_count_logarithmic` |
| `ZERO-KERNEL-UNIFORM-001` | Absolute convergence and all four rational ordinate-kernel bounds below | `zeroKernel_summable_bound`, `zeroKernel_distant_bound`, `zeroKernel_exterior_bound`, `zeroKernel_interior_bound` |
| `GLOBAL-TRIPLE-COUNT-001` | H_T(R)<=C T q^3(1+R)^4, R>=0 | `project_anchored_count_uniform` |
| `GLOBAL-TRIPLE-TAIL-001` | Normalized mass O(W A_p q^2), tail O_p(W A_p q^2 R^(4-p)), natural p>4 | `project_weighted_mass_tail`, `anchored_decay_twentieth_tail` |
| `KERNEL-HEIGHT-TRANSFER-001` | Same envelopes after multiplication by the actual rational kernel or any fixed horizontal partial; exact coefficient majorants | `actual_kernel_uniform_bounds`, `actual_horizontal_uniform_bounds`, `transferCoefficient_mass_bound`, `ordinateCoefficient_mass_bound` |

### Direct local Jensen proof

For a unit interval [v,v+1], put tau=v+1/2. If |tau|>=4, take center
c=2+i tau, inner radius 8/5 and outer radius 7/4. Every zero in that interval
with beta>=1/2 lies in the **closed** inner disk. On the outer disk,
Re(s)>=1/4, |Im(s)|>=1 and |s|<=|tau|+4. The checked estimates are

- |zeta(s)|<=3+2|s| on that quarter strip;
- |zeta(2+i tau)|>=1/4, for every real tau;
- the divisor mass in the inner disk is at most
  7 log(|tau|+2)/log(35/32).

The growth estimate adapts the pinned `Backlund/ZeroCountCrude.lean`
subband argument using `Zeta0EqZeta`, with its integral majorant extended from
Re(s)>=1/2 to Re(s)>=1/4. The center lower bound uses the absolutely convergent
Dirichlet series and the sum of n^(-2). Mathlib's analytic Jensen inequality
permits boundary zeros; no radius avoiding zeros is selected. Analytic divisor
orders are identified with occurrence multiplicities before comparing sums.
Horizontal reflection injects the left half of the strip into the right half
without changing ordinates or multiplicities. Consequently the high interval
count is bounded by 28 log(|v|+2)/log(35/32).

If |tau|<4, every occurrence in [v,v+1] lies in |gamma|<=5. Thus one possible
local constant is

    28/log(35/32) + card(occurrenceCutoff 5)/log 2.

This proves a single all-real-v bound, including ordinates below 3 and any
possible ordinate zero, without importing an exclusion theorem for that range.
The general interval bound, for v<=w, is

    C (w-v+1) log(max(|v|,|w|)+2).

Cover [v,w] by the closed unit intervals starting at v+n for
0<=n<=floor(w-v). Overlap only increases this upper bound. Empty intervals,
endpoint membership, and equality of cumulative cutoffs with [-U,U] are checked.
For U>=1, the cumulative bound implies the usual O(U log(U+2)) upper estimate;
it supplies neither the Riemann--von Mangoldt main term nor a matching lower count.

### Kernel sums and boundary conventions

All the following constants are uniform over the displayed ranges.

1. For all real t, sum_rho kappa(t-gamma) <= C log(|t|+2).
2. For T>=3, Z>=2T and 0<=t<=T,
   sum_{|gamma|>Z} kappa(t-gamma) <= C log Z/Z.
3. For T>=0 and 0<=t<=T,
   sum_{gamma<=0 or gamma>T} kappa(t-gamma)
   <= C log(T+2) [1/(1+t)+1/(1+T-t)].
4. For T>=3 and t<=0 or t>=T,
   sum_{0<gamma<=T} kappa(t-gamma)
   <= C log(T+2)/(1+dist(t,[0,T])).

Here `heightIntervalDistance T t=max(0,-t,t-T)` gives the elementary real
interval distance. The endpoints t=0,T are allowed, and the interior zero
interval is precisely (0,T]. Absolute convergence of every restricted sum
follows by restriction of the checked global positive summable series.

A stronger common tool is

    sum_{|t-gamma|>=a} kappa(t-gamma)
      <= C log(|t|+a+2)/(1+a),  a>=0.

For this proof partition the indicated occurrences by the dyadic index of
(|t-gamma|-a)/(1+a). At index n the count is bounded by a constant times
(1+a)2^n(n+3)log(|t|+a+2), while kappa is at most
2/((1+a)^2 4^n). The resulting series is summable because
sum_{n>=0}(n+3)2^(-n)=8. The finite interior bound uses its cardinality when
its distance from t exceeds T, avoiding a spurious log|t| in bound 4.

### Global triple count and decay

The centered interval bound is C(1+r)log(|t|+r+2). There are O(Tq) anchors.
For an anchor gamma1 in [T,2T], each partner in radius R has at most
C(1+R)log(2T+R+2)<=3C q(1+R)^2 possibilities. Multiplying the two partner
counts and summing over anchors gives H_T(R)<=C Tq^3(1+R)^4. Partners may
lie outside the anchor window; every such occurrence remains counted.

Let |w(x)|<=W on [T,2T] and, for a natural p>4, suppose

    |F(u,v)| <= A_p/(1+max(|u|,|v|))^p,    W,A_p>=0.

For f(t)=w(gamma1)F(ell(gamma2-gamma1),ell(gamma3-gamma1)), Lean proves
absolute summability and

    sum |f|/(Tq) <= C_p W A_p q^2,
    sum_{r>R}|f|/(Tq) <= C_p W A_p q^2/R^(p-4),  R>=1.

The generic theorem gives the stronger denominator (1+R)^(p-4) for R>=0
and also treats closed tails r>=R. Rescaled dyadic shells have cardinality
at most C Tq^3(1+R)^4 16^n and decay at most
A_p/((1+R)^p 2^(np)). Their geometric ratio is 2^(4-p)<1.
All regroupings use proved summability. At p=20 and R=q^(1/4), the normalized
strict tail is at most C W A_20/q^2. The arbitrary function envelope theorem
uses A=W A_20 for this specialization.

The exact real-space envelope is the hypothesis here. No Fourier-support
hypothesis is needed for these counting estimates. These estimates do not
provide a height-independent envelope for tests evaluated at complex arguments.

### Rational kernels, horizontal jets and normalizations

Multiplication by a factor of norm at most B replaces A_p by B A_p in both
mass and tail bounds. For actual tuples the previous milestones discharge B:
7 pi/9 for the rational kernel, and 4^(n+3)n! pi for a horizontal partial of
order n. Thus the same bounds apply to the identified integral profile and
all fixed horizontal orders, including repeated centers and endpoints.

For an absolutely norm-summable anchored f, the checked coefficient bounds are

    |transferCoefficient(T) sum f| <= (16/3) sum|f|/(Tq),
    |ordinateCoefficient(T) sum f| <= 4 pi sum|f|/(Tq).

The latter uses q<=4 pi ell above T0. The exact fixed-height transfer identity
and its ratio of logarithms remain the previously checked identity; this
milestone supplies uniform majorants, not a cancellation theorem.

## Dependency and verification record

The pinned mathlib Jensen theorem is `AnalyticOnNhd.sum_divisor_le`.
The explicit imported axiom reports also cover `Zeta0EqZeta`,
`zeta_eq_tsum_one_div_nat_add_one_cpow`, and `hasSum_zeta_two`.
Their pinned source paths and revisions are in the reproduction manifest.

The local count avoids the unproved `IEANTN/Kadiri.lean` `backlund_bound`
and `IEANTN/ZetaSummary.lean` `HSW.main_theorem` in the pinned dependency.
Neither is used to discharge a counting premise. All new solution theorems
are included in the axiom report; only `propext`, `Classical.choice` and
`Quot.sound` are permitted. No external-kernel run is claimed.

The inventory lists **73** new public theorems. **65** have definition-only
Comparator specifications. Eight finite-shell/finite-anchor helpers have
solution build and axiom checks; their types mention proof-built finite-shell
objects or the proved finite anchor instance, so they are not imported into
the definition-only challenge. The local-count unfinished-proof negative
control must be rejected for `sorryAx`. Every headline result in the table
has a Comparator specification.

Reproduce with:

```bash
python3 -B scripts/reproduce_lean.py --skip-bootstrap --fresh-project
```

## Remaining analytic work

The full `PAIR-COUNT-001` claim remains partial: Riemann--von Mangoldt,
its asymptotic main term and exclusion of real strip zeros are separate.
The historical `PAIR-COUNT-KERNEL-001` effectiveness scope is not promoted.
The full `ORDINATE-COUNT-001` also remains partial: the pair-dependent near
bound O(Tq^2 R^2) and stronger normalized O(q) total mass are not derived here.
The next analytic inputs are the pair explicit formula and prime-side estimates
needed for that near bound. The smoothed triple main term, error budget and
signed complex-argument o(1) still require their own formal proofs or research.

Historical closure decisions, proof drafts and audit snapshots keep their
original meanings. New ledger entries record precisely these checked pieces.
