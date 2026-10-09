# Lean milestone 3: horizontal-square lower bound

Task: formal verification. Assumptions: `UNCONDITIONAL`. The explicit finite
displacement examples are `SYNTHETIC_MODEL`, not assertions about zeta zeros.

**Verified:** the fresh project run on 2026-10-08 passed all 19 new
Comparator declarations, retained the earlier proof checks, rejected all
three unfinished-proof controls, checked 60 distinct axiom reports, and
passed 70 pair plus 126 triple regression tests. The complete logs and
source hashes are in the [verification archive](../artifacts/certificates/lean/a0d876dfc65c219ae378b452dc4e5a6302895c48f4d623f868e3f591cd7a1538/manifest.json).

The subsequent [summability milestone](lean-summability.md) adds
integration and infinite-sum implications. The archived counts below
describe milestone 3.

## Exact statement and conventional proof

For every real $x$,
\[
 \cosh x=\sum_{n=0}^{\infty}\frac{x^{2n}}{(2n)!}
 \ge 1+\frac{x^2}{2}.
\]
The equality is mathlib's `Real.hasSum_cosh` at the pinned mathlib revision.
Every summand is nonnegative for real $x$, and the proved `HasSum`
justifies retaining the terms $n=0,1$. This is not a formal manipulation
of a possibly divergent series.

Write $u_j=a_j^2/2\ge0$. Multiplying the three lower bounds gives
\[
 \prod_{j=0}^{2}\cosh(a_j)
 \ge\prod_{j=0}^{2}(1+u_j)
 \ge1+u_0+u_1+u_2.
\]
The second inequality discards only nonnegative cross-products. Hence
\[
 \boxed{\prod_{j=0}^{2}\cosh(a_j)-1
 \ge\frac{a_0^2+a_1^2+a_2^2}{2}.}
\]
No sign restriction on the $a_j$, small-argument expansion, or asymptotic
remainder is used.

## Same-ordinate sum with multiplicities

Let $D$ be a finite set of **occurrence indices** and let

\[
 m_D=|D|,\qquad Q_D=\sum_{i\in D}\delta_i^2,
 \qquad P(\xi,\eta)=\xi^2+\xi\eta+\eta^2.
\]

Different indices may carry the same complex value and displacement.
Define the real excess
\[
 G_{ijk}=
 \cosh\bigl(b\delta_i(\xi+\eta)\bigr)
 \cosh(b\delta_j\xi)\cosh(b\delta_k\eta)-1,
 \qquad B_D=\sum_{i\in D}\sum_{j\in D}\sum_{k\in D}G_{ijk}.
\]
These nested sums run over the full ordered Cartesian cube, including all
index coincidences. They use the same occurrence convention as the finite
foundation. No image set of distinct displacements replaces $D$.

The substituted pointwise inequality is
\[
 G_{ijk}\ge\frac{b^2}{2}
 \left[\delta_i^2(\xi+\eta)^2+\delta_j^2\xi^2+\delta_k^2\eta^2\right].
\]
For each slot, the other two indices have exactly $m_D^2$ choices.
Consequently the exact square-sum identity is
\[
 \sum_{i,j,k\in D}
 [\delta_i^2(\xi+\eta)^2+\delta_j^2\xi^2+\delta_k^2\eta^2]
 =2m_D^2Q_D P(\xi,\eta).
\]
This proves
\[
 \boxed{B_D\ge b^2m_D^2Q_D P(\xi,\eta)\ge0.}
\]
The proof applies to any finite $D$ and arbitrary real $b,\xi,\eta,\delta_i$.
Empty fibers are allowed. No reflection closure, cancellation of odd moments,
bound on the displacement, or simplicity assumption is required.

The frequency form satisfies
\[
 P(\xi,\eta)-\frac{\xi^2+\eta^2}{2}
 =\frac{(\xi+\eta)^2}{2}\ge0,
 \qquad P(\xi,\eta)=0\iff\xi=\eta=0.
\]
Thus both frequency axes and the line $\xi+\eta=0$ are included. At the
frequency origin, or when $b=0$, the excess sum itself is zero.

## Nonnegative ordinate weights

For a finite occurrence set $D$, an ordinate label map $\gamma:I\to A$,
and $g\in\gamma(D)$, define
\[
 D_g=\{i\in D:\gamma_i=g\}.
\]
The formal label type $A$ is arbitrary with decidable equality; for real
ordinates the usual classical instance is permitted. This is not a numerical
algorithm for deciding equality of real ordinates.

For $W(g)\ge0$ on the finite image $\gamma(D)$, summing the fiber bounds
gives
\[
 \sum_{g\in\gamma(D)}W(g)B_{D_g}
 \ge b^2P(\xi,\eta)
       \sum_{g\in\gamma(D)}W(g)m_{D_g}^2Q_{D_g}.
\]
Weights outside this image are unrestricted. Nonnegative weights are an
explicit hypothesis; a sign-changing height weight is not covered by this
inequality. Within each fiber all ordered triples, including repetitions,
are retained.

## Formal declarations and verification

The definition-only module `HorizontalSquareDefinitions` contains the
excess, square mass, frequency form, nested triple sum, and ordinate fiber.
The solution module `HorizontalSquare` proves the following theorem families:

| Family | Declarations |
| --- | --- |
| Scalar and triple bounds | `cosh_quadratic_lower`, `cosh_triple_quadratic_lower`, `horizontal_cosh_square_lower` |
| Frequency form | `horizontal_frequency_lower`, `horizontal_frequency_nonneg`, `horizontal_frequency_zero_iff` |
| Square mass and finite sums | `horizontal_square_mass_nonneg`, `horizontal_cube_square_sum`, `same_ordinate_horizontal_square_lower`, `same_ordinate_cosh_nonneg`, `weighted_ordinate_fibers_lower` |

Eight further named example theorems cover mixed signs, empty fibers,
singletons, zero scale, the frequency origin, axes and the anti-diagonal,
repeated occurrences, and unequal fiber multiplicities. For the occurrence
displacements $(1,1,-1)$, the lower-bound coefficient is $m^2Q=27$, not
the coefficient obtained by collapsing to distinct displacement values.
These are exact Lean proofs, with no floating-point evaluations of cosh.

The Comparator challenge checks all 19 declarations using only the
definition module as its shared specification. An unfinished solution must
be rejected for `sorryAx`. Solutions contain no `sorry`, extra axioms, or
`native_decide`. The solution imports are mathlib-only and exclude quasi-RH.

Run the full reproduction suite with

```bash
python3 -B scripts/reproduce_lean.py --fresh-project
```

Existing installations may use `--skip-bootstrap`. The runner retains all
earlier Comparator checks, adds this challenge and its negative control,
checks 60 distinct axiom reports, and runs the pair/triple regression suites.
Only `propext`, `Quot.sound`, and `Classical.choice` are permitted. A fresh
project build reuses dependency caches; it is not an independent-kernel check.

## Connection to the research observable and limits of coverage

Use $b=\log(T/(2\pi))$ and $\delta_i=\beta_i-1/2$. Lean's slots $0,1,2$
match the manuscript's anchor-first slots $1,2,3$. When all three ordinates
are equal, both real vertical gaps vanish and the Fourier phase is one.
The theorem bounds the real cosh excess that occurs there after sign averaging.
For $T>1$, writing $q=\log T$ and $x_i=q\delta_i$ translates its lower
bound to $(b/q)^2m_D^2P(\xi,\eta)\sum_{i\in D}x_i^2$. This is a change
of normalization, not a claim that the horizontal moment tends to zero.

This milestone does not formalize the analytic identification of that excess
with the original complex test expression, integration against a nonnegative
Fourier test, removal of infinite zero cutoffs, or positivity of the whole
signed error. In particular, unequal-ordinate terms retain their oscillatory
phases, and a general Fourier test need not be nonnegative. The full
ordinate-only $o(1)$ estimate remains open.

Apart from the already proved scalar cosh series, every sum introduced here
is finite. There is no height limit, Fourier-support restriction, or exchange
of infinite zero sums and integrals. New ledger entries and evidence remain
outside the historical pair and triple RH audits.
