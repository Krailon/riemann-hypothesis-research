# Lean milestone 2: finite correlation foundations

The subsequent [horizontal-square milestone](lean-horizontal-square.md)
extends the runner with a separate inequality challenge. The archived run
and declaration counts below describe milestone 2.

Task: formal verification. Assumptions: `UNCONDITIONAL`; explicit point
configurations in the example suite are `SYNTHETIC_MODEL`, not zeta data.

**Verified:** the [fresh-project run](../artifacts/certificates/lean/8a49b4e7f3beb2d96650295eaaede990f943c40ca4b9030a587dbfcbe36e8e41/manifest.json)
passed the 35-declaration finite challenge, both existing Comparator checks,
both unfinished-proof rejection controls, all 41 distinct axiom reports,
and the 70 pair plus 126 triple regression tests. Source and output hashes
were checked against the archived manifest. Dependency caches and the pinned
tools were reused; the project build directory was moved aside. This is a
fresh project build in a development worktree, not a clean-checkout claim.

## Conventions and five patterns

An occurrence type `I` labels copies separately. A map `ρ : I → ℂ` need not
be injective. A triple is `t : Fin 3 → I`; Lean slots 0, 1, 2 correspond to
manuscript slots 1, 2, 3, with slot 0 the anchor. A label map `q : I → A`
can be the index itself, the complex value, or the ordinate. These give
different partitions. For ordinates take `q i = (ρ i).im`.

| Constructor | Exact condition on labels `v = q ∘ t` |
| --- | --- |
| `allEqual` | `v 0 = v 1` and `v 1 = v 2` |
| `only01` | `v 0 = v 1` and `v 0 ≠ v 2` |
| `only02` | `v 0 = v 2` and `v 0 ≠ v 1` |
| `only12` | `v 1 = v 2` and `v 0 ≠ v 1` |
| `allDistinct` | All three pairwise inequalities |

`classifyTriple_iff`, `pattern_unique`, and `pattern_disjoint` certify that
these conditions agree with the classifier and are exhaustive and disjoint.
Decidable equality is a formal parameter, not a claim that real-number
equality can be decided numerically.

## Regrouping and preservation of multiplicity

Let `S j` be a finite set of occurrence indices for slot `j`. The triple
domain is their Cartesian product, `Fintype.piFinset S`. The sets may differ
between slots and may be empty. Equal indices and equal values are allowed.

`sum_triple_patterns` decomposes an arbitrary sum over this domain into the
five filtered pattern sums. Its values lie in any additive commutative monoid.
No sign, symmetry, or positivity condition on the summand is required.

For a finite domain `D` and any label map `q`, `sum_regroup_fibers` proves

\[
\sum_{i\in D} f(i)
=\sum_{a\in q(D)}\sum_{\substack{i\in D\\q(i)=a}} f(i).
\]

When `f = g ∘ q`, `sum_regroup_multiplicity` replaces the inner sum by
`#{i∈D : q i=a} • g a`. Thus indexing by distinct labels retains the size
of each fiber. The example with labels `(0,0,1)` and weights `(2,2,5)` has
occurrence sum 9, whereas an unweighted sum over distinct labels is 7.

## Finite reflection identities

The input is an occurrence involution `r : I → I`, with
`r (r i) = i`. For each slot, require `i∈S j → r i∈S j`. For the ordinate
partition also require `q (r i) = q i`. These are explicit hypotheses.
They are not inferred from distinct complex values or from pointwise zero
symmetry, and no global enumeration of zeta zeros is constructed here.

A mask `e : Fin 3 → Bool` chooses which slots to reflect. `true` reflects
and has sign −1; `false` leaves the slot fixed and has sign +1.

- `reflectSlots_involutive` and `reflectSlots_bijective` give the tuple
  bijection; `reflectSlots_domain` verifies the finite cutoff condition.
- `reflectSlots_labels` and `reflectSlots_pattern` preserve the entire label
  tuple and hence its ordinate-equality pattern.
- `sum_involution`, `sum_reflectSlots`, and `sum_reflectSlots_pattern` prove
  reindexing of arbitrary finite sums, including each ordinate-pattern sum.
- `sum_eight_reflections` and its pattern version average those identities
  over the eight masks, with exact complex coefficient `1/8`.
- `simultaneous_index_pattern` preserves index equalities when every slot
  is reflected. `independent_index_counterexample` shows that reflecting
  only the first coordinate of `(false,false,false)` under Boolean negation
  changes `allEqual` to `only12`.

Thus the manuscript's warning about index diagonals remains valid. Its finite
reindexing step can also be applied separately to ordinate-equality classes.
All sums here are finite: there are no cutoff limits or Fubini claims.

## Eight-sign algebra

For arbitrary complex coefficients `C j`, `S j` and an arbitrary function
`K` on the eight masks, define

\[
K_A=\frac18\sum_\varepsilon
\left(\prod_{j\in A}\varepsilon_j\right)K(\varepsilon).
\]

`sign_product_expansion` and `weighted_sign_product` give the finite product
expansion. `weighted_sign_sub_one` and `weighted_sign_empty_split` establish

\[
\frac18\sum_\varepsilon K(\varepsilon)
\left(\prod_j(C_j+\varepsilon_jS_j)-1\right)
=K_\varnothing\left(\prod_j C_j-1\right)
+\sum_{A\ne\varnothing}K_A\prod_{j\in A}S_j\prod_{j\notin A}C_j.
\]

This is the finite algebra in `ORDINATE-SIGN-AVERAGE-001`. Substitution of
hyperbolic functions, the analytic kernel, integrations, and infinite zero
sums are not formalized by this algebraic statement. In particular it makes
no positivity or cancellation assertion about the surviving signed error.

## Pointwise zeta adapter

`horizontalReflection ρ = 1 − conj ρ`. The mathlib-only `ZeroReflection`
module proves its involutivity, preservation of the ordinate, negation of
`Re ρ − 1/2`, and preservation of `IsCriticalStripZero`.

The existing `reflected_zero` declaration for `1 − ρ` was moved here without
changing its statement or name. It uses `riemannZeta_one_sub`; the new
horizontal symmetry also uses mathlib's `riemannZeta_conj`. Neither needs
the quasi-RH import. `HorizontalStrip` now imports this module, and its
original Comparator challenge continues to check all six old statements.
Pointwise symmetry does not by itself supply an occurrence involution or
prove equality of analytic zero multiplicities.

## Verification and relation to earlier claims

`HigherCorrelations.FiniteFoundation` collects the solutions. The challenge
imports only definition modules and checks 35 declarations, including eight
named example theorems. Its intentional `sorry` specifications are never
imported by solutions. An unfinished finite solution must be rejected for
`sorryAx`, in addition to the earlier negative control.

The example suite covers all patterns, empty and singleton products, different
slot cutoffs, duplicate occurrences, different complex values at one ordinate,
fixed points, and exchanged pairs. Proofs use Lean's ordinary kernel; there
is no floating-point or `native_decide` certificate.

Run the extended full harness:

```bash
python3 -B scripts/reproduce_lean.py --fresh-project
```

Use `--skip-bootstrap` only when the pinned tools are already installed.
The run builds the finite foundation, checks its Comparator challenge and
negative control, retains the upstream and strip checks, and validates 41
distinct axiom reports plus the pair/triple regression suites. Only
`propext`, `Quot.sound`, and `Classical.choice` are permitted; declarations
with no axioms are also accepted. No independent external kernel is claimed.

Proof-level dependencies within the project are: pattern definitions →
pattern partition/regrouping; occurrence reflection and finite reindexing →
eight-reflection averages; finite product distributivity → sign expansion;
mathlib functional equation and conjugation → pointwise zero reflection.
The imported quasi-RH theorem is absent from the new solution import closure.

The corresponding new ledger entries are separate from the historical pair
and triple claims. This milestone verifies finite foundations, not the
convergence proofs or the full analytic statements of Work Packages A/B.
The ordinate-only `o(1)` target remains open.
