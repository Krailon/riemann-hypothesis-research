# Uniform named pair explicit-formula errors

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
New ledger claim: `PAIR-UNIFORM-FORMAL-001`.

## Statement

`HigherCorrelations.pairUniform_formula` reconstructs `PAIR-EF-001`:

    S(X,t) = -P(X,t) + X^(-1) log(|t|+2)
             + E_arch(X,t) + E_DS(X,t) + E_pole(X,t) + E_trivial(X,t).

For every real X≥1 and real t, `pairUniform_named_bounds` proves

    |E_arch|    ≤ C_arch / X
    |E_DS|      ≤ C_DS / X
    |E_pole|    ≤ 4 X^(1/2) / (1+t²)
    |E_trivial| ≤ 12 X^(-5/2) / (|t|+2).

The errors have exactly the definitions recorded in `PAIR-EF-001`.
The chi factor uses exp(z log 2), exp((z−1) log π), sin(πz/2), and
Gamma(1−z); positive-real powers use the existing exponential convention.
The principal complex logarithm is retained. All actual zero occurrences,
both ordinate signs, and analytic multiplicities remain in S.

The explicit archimedean constant is
C_arch = log(2π)+π+log 2+4/3. The Dirichlet constant is the convergent
series C_DS = Σ_{n≥2} Λ(n)n^(−3/2); the Lean indexing begins at n=1,
whose von Mangoldt term is zero. Its approximation by terms n≤N has
nonnegative remainder at most 16 N^(−1/4), for N≥1. This deliberately
coarse tail proves effectiveness without a numerical evaluation.

`pairUniform_remainder_bound` combines the four bounds only after each
has been established uniformly. Endpoint and zero-height corollaries
are supplied. Negative t, prime-power knots, and t equal to any zero
ordinate are covered by the unrestricted real parameter; the earlier
weight-one prime-knot convention is unchanged.

## Proof and convergence

1. Differentiate the unconditional zeta functional equation on Re(w)<0
   using the exact chi factor. At w=−1/2+it, its factors do not vanish,
   including at t=0. This splits the existing shifted logarithmic derivative.
2. Derive the digamma remainder from the audited right-half-plane series.
   For each finite N, compare Σ_{n<N}(z+n)⁻¹ with log(z+N)−log z.
   Each unit interval has error at most
   2(1/(|z|+n)−1/(|z|+n+1)); these bounds telescope.
   The harmonic-number limit and log((z+N)/(N+1))→0 then prove
   |psi(z)−log z|≤2/|z| for every Re(z)>0. No infinite sum is
   interchanged with an improper integral.
3. At z=3/2−it, bound the principal log by log(|t|+2) with error
   log 2+π/2. The cotangent factor at −π/4+iπt/2 has norm one.
   Together these give the explicit C_arch.
4. Apply the absolutely convergent Euler series at Re(z)=3/2.
   For effectiveness, Λ(n)≤log n≤4 n^(1/4), followed by the integral
   test, gives the stated C_DS tail.
5. Bound the pole denominator below by (1+t²)/2. For trivial zeros,
   retain X^(−5/2) in the numerator and the m²+t² denominator.
   Finite reciprocal-square sums telescope; split |t|≤1 and |t|>1
   before passing to the absolutely convergent sum.
6. Insert these identities and bounds into the already formalized exact
   pair formula. No simultaneous X,t limit or asymptotic hypothesis is needed.

This establishes the full named-error statement. It does not formalize
the larger fixed-sector assertion of `GAMMA-DIGAMMA-001`, the sharper
historical contour bounds, prime-side mean-square asymptotics, or the
triple theorem.

## Verification

The [inventory](lean-pair-uniform-inventory.json) contains 37 public
theorems in eight modules. Every public theorem and the imported digamma
series receive transitive axiom reports. Fifteen specifications are
checked by Comparator in a separate environment importing only the error
definitions and general library infrastructure. An intentionally unfinished
solution must be rejected. Solution modules never import challenge modules.

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Nanoda remains disabled. This is Lean proof verification, not numerical
evidence. The full reproduction command is:

```sh
python3 scripts/reproduce_lean.py --skip-bootstrap
```

Full reproduction passed and is archived in
[`d20c9ee6c70d…`](../artifacts/certificates/lean/d20c9ee6c70dd65db04e8e9d11f3f80ef0c6115c9045fa3a5b46700e5c41a4e6/manifest.json).
The run passed all 48 commands, including 15 new Comparator specifications,
559 total transitive axiom reports, 12 unfinished-proof rejection controls,
20 coverage checks, 70 pair regressions and 126 triple regressions.
All recorded source and output hashes were verified against the archive.
This run used the existing build cache (`fresh_project_build=false`);
it is not a claim of fresh-checkout or external-kernel verification.

## Next step

The [Fourier mean-value input](lean-pair-meanvalue.md) is now checked and
specialized to the actual prime series, and the
[weighted nearby-prime sieve bound](lean-pair-sieve.md) is checked.
The [prime diagonal asymptotic](lean-pair-diagonal.md) is now checked with
existential constants, as is the [optimized prime mean square](lean-pair-prime-mean.md).
The [full RHS mean square](lean-pair-rhs-mean.md) now combines these inputs.
Next assemble the normalized pair-correlation asymptotic.
