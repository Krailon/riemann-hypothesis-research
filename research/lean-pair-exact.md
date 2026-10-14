# Exact pair explicit formula

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
This follows the [paired Mellin milestone](lean-paired-mellin.md).
New ledger claim: `PAIR-EXACT-FORMAL-001`.

## Statement and conventions

For every real X≥1 and real t, set s=1/2+it. The headline theorem
`HigherCorrelations.pairExact_formula` proves

    S(X,t) = -P(X,t) - X^(-1) ζ'(s-1)/ζ(s-1)
             + 2 X^(1-s)/(s(2-s))
             + 2 Σ_{m≥1} X^(-2m-s)/((2m+s-1)(2m+s+1)).

S and P are exactly the [existing series definitions](../lean/HigherCorrelations/PairSeriesDefinitions.lean).
The zero index is an actual complex zero together with an analytic-multiplicity
index. Both ordinate signs are included; equal ordinates and repeated zeros
are retained. No replacement of β by 1/2 occurs. Powers of positive real
numbers use exp(z log X).

The endpoint theorem proves the same identity at X=1 for every real t,
including t=0. The trivial-zero series is absolutely and uniformly
convergent on X≥1, t∈R by the majorant 2/m². Existing continuity and
prime-knot results apply; a prime summand with n=X has weight one.
There are no endpoint half-weights or principal-value zero sums.

## Proof and limit order

1. Expand -ζ'/ζ on Re(z)=5/2 into its absolutely convergent Euler series.
   An explicit integrable majorant justifies termwise integration.
   The paired Mellin evaluation gives the exact prime-side identity.
2. Compute residues at the nontrivial zeros, the pole at 1, the two
   kernel poles s±1, and the trivial zeros -2m. Simplicity is proved
   only for the trivial zeros. Nontrivial residues retain their
   analytic orders and are regrouped into occurrence sums.
3. Select heights U_n∈(n+2,n+3), with separation at least
   1/(C log(n+6)) from every zero ordinate, at both signs.
4. For fixed M, X≥1, and t, the Hadamard expansion of xi and the
   digamma bounds give an O_M(H^(7/4)) logarithmic-derivative bound
   along these heights. The quadratic kernel gives a uniform
   O_{X,t,M}(H^(-1/4)) horizontal integrand bound. Both horizontal
   integrals tend to zero.
5. Apply the finite rectangle residue theorem between Re(z)=5/2 and
   Re(z)=-(2M+1). Prove that all candidate poles lie strictly inside,
   that the integrand is analytic elsewhere, and that its poles
   have order at most one. A removable candidate contributes zero.
6. Let the height tend to infinity at fixed X>1, t, M. Absolute
   zero-series convergence and vertical integrability give the
   infinite-height identity.
7. Let M tend to infinity with X>1 and t fixed. On the left line,
   the logarithmic derivative is bounded by C+G log(|v|+2)+2M
   away from the measure-zero point v=0. The kernel is bounded by
   8 exp(-(2M+3/2)log X)/(1+(v-t)²). The logarithmic weight is
   integrable, and exponential decay absorbs the linear M factor.
8. Finally let X decrease to 1, using the already checked continuity
   of S and P, uniform convergence of the trivial series, and
   continuity of the two elementary corrections.

The proof supplies the exact identity by this sufficient, coarser contour
bound. It does **not** formalize the historical O(log² H) contour estimate
or its sharper left-edge rate. It does not yet prove the uniform named
remainders of `PAIR-EF-001`, pair mean-square asymptotics, or the triple
theorem. The historical ledger and its audit remain unchanged in scope.

## Imported inputs and compatibility

The proof uses the pinned mathlib Euler-series, Mellin inversion,
meromorphic-order, convergence, and integration infrastructure, together
with audited PNT Hadamard factorization and rectangle residue results.
The source-specific xi-to-zeta logarithmic-derivative bridge, functional
equation for that derivative, pole classification, and all contour
limits are proved locally.

The pinned upstream `IEANTN.HadamardLogDerivative` and full `IEANTN.Kadiri`
modules could not be built against the pinned mathlib API. They are not
imported by the new proof. No upstream source was changed for this
milestone, and no unfinished upstream contour theorem is used.
The axiom audit checks dependencies transitively, including the imported
Hadamard and residue theorems.

## Verification

The [inventory](lean-pair-exact-inventory.json) records 106 public theorems
in 28 modules. Every public theorem receives a transitive axiom report.
The Comparator checks 23 selected specifications, including the complete
identity, endpoint, prime identity, residues, and contour limits, against
an independent challenge environment importing definitions and general
library infrastructure. The deliberately unfinished solution must be
rejected for `sorryAx`. Solution modules never import challenge modules.

The allowed axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The external Nanoda kernel is disabled, as in previous
milestones. This is Lean verification; it is not a numerical experiment.

Reproduce with:

```sh
python3 scripts/reproduce_lean.py --skip-bootstrap
python3 -m unittest discover -s scripts -p 'check_lean_analytic_coverage.py'
```

Local verification passed: 23 Comparator specifications, unfinished-proof rejection,
521 total axiom reports (including earlier milestones), 70 pair regressions,
126 triple regressions, and 19 coverage checks.

Full reproduction passed and is archived in
[`06f33fbfed84…`](../artifacts/certificates/lean/06f33fbfed84434b4c45b57e9da81ba193e4ce58f0665e6fc87a57a42ab6f89e/manifest.json).
The run includes 11 successful unfinished-proof rejection controls,
all 521 axiom reports, the complete project build, earlier Comparator
milestones, and the pair/triple regression suites. All recorded source
and output hashes were checked against the archive. This run used the
existing build cache (`fresh_project_build=false`); it is not a claim of
a fresh checkout or external-kernel verification.

## Next small step

Formalize the uniform named remainders in `PAIR-EF-001`, beginning with
the shifted logarithmic derivative and its archimedean/Dirichlet-series
split. The exact identity is now the available input for that task.
