# Pair explicit-formula series convergence

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
This follows the [uniform-height milestone](lean-uniform-height.md).

The new ledger claim is `PAIR-SERIES-CONVERGENCE-001`. It formalizes the
convergence portion of `PAIR-EF-CONVERGENCE-001` with an **existential
absolute tail constant**. The historical claim also asserts effectiveness;
its status and statement remain unchanged. The coverage map therefore marks
that historical claim as partial.

## Definitions and endpoint conventions

`PairSeriesDefinitions.lean` is the definition-only interface. For
p=(X,t), X>=1, t real, it defines

    S(X,t) = sum_rho 2 exp(log X (delta+i(gamma-t)))
                        / (1+((t-gamma)+i delta)^2),
    P(X,t) = sum_{n>=1} Lambda(n) exp(log n (-1/2-i t)) min(n/X,X/n).

Here delta=Re(rho)-1/2 remains symbolic. `ZeroOccurrence` uses the analytic
multiplicity of every zero in the open critical strip, with both signs of
gamma and any possible ordinate zero retained. No RH, simplicity, exclusion
of real strip zeros, or stronger zero-free strip is needed for these bounds.
The Lean prime index k is natural and represents n=k+1; Lambda(1)=0.
The exponential convention explicitly fixes all positive-base complex powers.

The parameter domain is the **closed** set [1,infinity) x R. Rectangles
are 1<=X<=B, |t|<=H; local uniform convergence uses neighborhoods relative
to this closed domain. The prime weight is continuous at every knot X=n,
where its value is exactly 1. At X=1 the zero numerator is exactly 2.
Both endpoint identities have separate Comparator specifications.

Zero height cutoffs include |gamma|=U. The complementary absolute tail is
strictly |gamma|>U. The cutoff parameter U is real and tends to infinity;
the prime partial sum over k<N is exactly the sum over 1<=n<=N.
The zero series is also proved convergent along arbitrary finite subsets,
so no principal-value ordering is required.

## Proof dependencies and bounds

1. Open-strip membership gives |delta|<=1/2. Taking the real part of the
   denominator gives its norm >=(3/4)(1+(t-gamma)^2), hence

       |zero term| <= (8/3) sqrt(X) kappa(t-gamma),
       kappa(v)=1/(1+v^2).

2. `zeroKernel_summable_bound` supplies absolute summability at every real t.
   On a rectangle the common summable majorant is

       (8/3) sqrt(B) (2+2H^2) kappa(-gamma).

   The elementary inequality kappa(t-gamma)<=
   (2+2H^2)kappa(gamma) applies when |t|<=H. Mathlib's Weierstrass
   theorem gives uniform convergence over finite zero subsets.

3. If U>=2(|t|+2), then U>=4 and |gamma|>U implies
   |t-gamma|>=U/2. Restriction of `zeroKernelTail_summable_bound` gives

       sum_{|gamma|>U} |zero term| <= C sqrt(X) log(U)/U.

   The proof applies to negative, zero and positive t without a reflection
   reindexing. Absolute convergence identifies the complement of the inclusive
   cutoff and bounds the norm of the complex remainder by this absolute tail.
   The constant inherits the previous milestone's unevaluated low-height count.

4. For 1<=X<=B the prime term is bounded by B Lambda(n)/n^(3/2),
   independently of t. Summability comes from pinned mathlib
   `ArithmeticFunction.LSeriesSummable_vonMangoldt` at s=3/2, in
   `Mathlib/NumberTheory/LSeries/Dirichlet.lean`. Its proof uses
   Lambda(n)<=log n and absolute Dirichlet-series convergence; no PNT,
   zero-density estimate, RH, or prime-correlation conjecture is imported.

5. Each summand is continuous on the closed domain. Local uniform convergence
   yields continuity of both sums. The only limits here are the summation
   cutoffs, uniformly on each fixed rectangle. No simultaneous unbounded-X
   or unbounded-t limit and no sum/integral interchange is asserted.

## Verification

The [inventory](lean-pair-series-inventory.json) lists 27 public declarations;
all have definition-only Comparator specifications and axiom reports.
The imported von Mangoldt convergence theorem also has an explicit axiom
report. Only `propext`, `Quot.sound` and `Classical.choice` are permitted.
A deliberately unfinished version of the assembled convergence statement
must be rejected for `sorryAx`. Challenge placeholders are isolated from
all solution imports. No external-kernel check is claimed.

Reproduce the full suite, including these new checks, with:

```bash
python3 -B scripts/reproduce_lean.py --skip-bootstrap --fresh-project
```

Verification passed on 2026-10-12: **27 new Comparator specifications**, **390
axiom reports**, **nine unfinished-proof controls**, **196 pair/triple
regressions**, and **17 coverage checks**.

The [fresh-project run](../artifacts/certificates/lean/d1f1a85d4b7b4557d2f7d5ec564017b2266c16cf2653c7aa313e6d0dc88e26b7/manifest.json)
passed every Lean check, then stopped because the triple audit's hash of the
updated pair audit was stale. That failed overall run is retained unchanged.
The [passing follow-up archive](../artifacts/certificates/lean/c216f17ccdadb2dc9ec50f1a5d14230a7150793a7451f0d2d83b3d02b53800d7/manifest.json)
verifies every base output hash and the unchanged proof/harness source hashes,
inherits the successful fresh-project proof checks, and records passing reruns
of all 196 regressions and 17 coverage checks after the metadata repair.
No Lean check was skipped on account of a proof failure; none failed.
The ledger's certificate field refers to this explicit combined record.

## Next dependency

Formalize `PAIR-EF-MELLIN-001`, including y=1, before assembling the exact
pair explicit formula. This milestone does not establish that equality,
prime-side asymptotics, or the still-open signed complex-argument o(1).
