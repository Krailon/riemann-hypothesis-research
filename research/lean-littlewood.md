# Littlewood rectangle counting

Assumptions: `UNCONDITIONAL`, with the explicitly stated analyticity and zero-free
boundary hypotheses. This milestone does not assume or prove `UniformDyadicDensity`.

## Interface and conventions

`LittlewoodRectangle f a b c d` asserts a<b, c<d, analyticity on a neighborhood
of every point of the closed rectangle [a,b]+i[c,d], and nonvanishing on its
entire boundary. Corners are included. The generic theorem applies to holomorphic
functions, not meromorphic functions with unaccounted poles. The finite zero set Z
is specified by exact membership; a separate theorem produces such a finite set.
The zero weight is `analyticOrderNatAt f ρ`. The horizontal count is the sum of
those weights for Re ρ>σ; equality at σ is excluded.

Choose any complex k with exp(k)=f(b+ic). Set q=f'/f and define transported logs

    B(x) = k + integral_b^x q(u+ic) du,
    R(t) = k + i integral_c^t q(b+iy) dy,
    U(x) = R(d) + integral_b^x q(u+id) du.

These are `littlewoodBottomLog`, `littlewoodRightLog`, and `littlewoodTopLog`.
Their exponential identities, derivatives and real parts are checked. The two
horizontal arguments are Im U and Im B, transported from the same base value
through the right edge. The principal logarithm is used only to choose an initial
value in the final zeta adapter. No logarithm is asserted on the whole closed loop
or across interior zeros. The boundary expression is independent of the valid
choice of k.

## Exact identity and count bound

Write

    M = sum_{ρ in Z} m(ρ)(Re ρ-a),
    A = integral_c^d log|f(a+it)| dt - integral_c^d log|f(b+it)| dt
          + integral_a^b (Im U(x)-Im B(x)) dx.

`littlewood_identity` proves 2π M=A. The contour is counterclockwise; the project
uses `RectangleIntegral'=(2πi)^(-1) RectangleIntegral`. The proof specializes
`Zeta23.Analytic.rectangleIntegral'_mul_logDeriv` to weight s-(a+ic), then performs
four one-dimensional integrations by parts. A separately transported left-edge
log has the same real part at the top-left corner as U, which suffices for the
imaginary-part cancellation. All boundary integrands are interval integrable.

For every σ>a, `littlewood_mass_count` gives (σ-a)N_f(σ)≤M. Consequently

    N_f(σ) ≤ A / (2π(σ-a)),
    A≤E  implies  N_f(σ) ≤ E / (2π(σ-a)).

This is a finite inequality. No infinite sums, limiting operations, or unproved
sum/integral interchanges occur. The theorem also works for σ>b, when the strict
tail is empty; no upper restriction on σ is needed in the generic bound.

## Actual zeta specialization

`littlewood_zeta_count` identifies the generic multiplicity sum at right edge 2
with `(rightDensityWindow c d (σ-1/2)).card`. Its proof gives an explicit bijection
between the filtered complex zeros and filtered `StripZero` values, and uses the
existing analytic-multiplicity identity for actual occurrences. There is no
simplicity assumption and no replacement of β by 1/2.

The closed-rectangle lower endpoint γ=c cannot contain a counted zero because
it lies on the assumed zero-free boundary. This justifies the identification
with the project's half-open convention c<γ≤d; zeros on γ=d are likewise excluded
by that same hypothesis, not silently discarded.

`littlewood_zeta_budget_positive_height` takes 0<a<σ<1, 0<c<d, nonvanishing of
zeta on the border, and A≤E with k=log ζ(2+ic). It proves the displayed bound for
actual occurrences. Zeta analyticity follows on the positive-imaginary half-plane;
the rectangle avoids its pole. Nonvanishing on Re s=2 supplies the base logarithm.

## Products and mollified zeta

For analytic f and g, boundary nonvanishing of fg implies boundary nonvanishing
of each factor. `littlewood_product_factors` extracts both rectangle hypotheses;
`LittlewoodRectangle.mul` constructs the product hypothesis from the factors.
Interior zeros of either factor remain allowed.

`LittlewoodRectangle.order_finite` uses the connected closed rectangle and a
nonzero corner value to prove that the analytic order is finite at every point
of the rectangle. Consequently `littlewood_product_order` proves

    order(fg,s) = order(f,s) + order(g,s),

with natural analytic orders and no remaining finite-order hypothesis. This
step is essential because converting an infinite extended order to a natural
number would otherwise discard it. For exact finite zero sets Zf,Zg,Zfg,
`littlewood_product_count_add` proves, for every real sigma,

    N_fg(sigma) = N_f(sigma) + N_g(sigma).

The product zero set is their union, but its weights add at common zeros. The
proof extends both weighted sums to the product zero set using zero order at
nonzeros, so shared roots and additional roots of g are treated exactly.

For F=zeta*M, `littlewood_mollified_occurrence_order` gives the original zeta
multiplicity plus the order of M at each actual occurrence. The count inequality
then combines with Littlewood to give

    # {i : c<gamma_i<=d, beta_i>sigma}
       <= A_F/(2pi(sigma-a)),
    A_F<=E implies the same count <= E/(2pi(sigma-a)).

The convenience theorem `littlewood_mollified_budget_positive_height` assumes
0<a<sigma<1, 0<c<d, M analytic near [a,2]+i[c,d], and F nonzero on the entire
border. Zeta analyticity and both factor boundary conditions are proved from
these hypotheses; neither factor is required to be nonzero in the interior.
Its base logarithm is `Complex.log (F (2+ic))`. The general bound accepts any k
with exp(k)=F(2+ic); no identity between independently chosen principal logs is
used. The generic M is an analytic multiplier: choosing Dirichlet-polynomial
coefficients or proving mollifier mean-square estimates is outside this step.

Checks cover M=1, arbitrary nonzero constant multipliers, shared repeated roots,
additional distinct roots, strict threshold equality, and the impossibility of
a zero multiplier satisfying the rectangle boundary condition. Shared roots
contribute m+n, including when their ordinates coincide; distinct added roots
are counted separately with their own multiplicities.

## Verification and provenance

The existing pinned and ported Zeta23 weighted argument principle is reused
without modifying vendored sources. Its axiom report is included explicitly, in
addition to all project declarations. Mathlib supplies analytic orders, real-path
calculus for complex functions, the fundamental theorem of calculus, finite-sum
inequalities, and elementary zeta analyticity/nonvanishing.

The suite contains 56 public statements in ten modules (20 statements in three
modules were added for products and mollified zeta). Definition-only
Comparator contracts cover every statement. Sixteen unfinished controls cover log
transport, integrability, contour orientation, the weighted argument principle,
the identity, count bounds, actual zeta specialization, constant functions,
repeated zeros, threshold exclusion, branch invariance, product factors, finite
orders, order additivity, count additivity and the mollified-zeta budget. Checked examples give
A=0 for a nonzero constant and A=2πm(Re ρ-a) for (s-ρ)^m with ρ strictly interior.
Only `propext`, `Quot.sound` and `Classical.choice` are permitted; Nanoda is not run.
Python regression tests verify inventory, scope and harness behavior, not analysis.

    python3 scripts/reproduce_lean.py --reuse-dependencies --littlewood-only --control-jobs 8

The default reproduction includes this suite. The focused run also builds the
combined project, audits all registered axioms, and runs coverage, harness,
control-pool and pair/triple regressions. Its content-addressed manifest is linked
from the appended formal ledger entry.

## Remaining density work

The exact bridge from a boundary integral budget to horizontal counts is now
checked on zero-free boundaries. Removing that boundary restriction needs a
separate limiting argument with the correct strict/half-open conventions.
Mollified-zeta order and count comparisons are now checked. Mollifier and twisted
second-moment estimates and the uniform density theorem remain further work. In particular, this lemma
does not instantiate `UniformDyadicDensity`, prove a close-pair bound, establish
a density-based moment estimate, or settle the signed complex-argument error.
Historical density and pair/triple theorem statuses remain unchanged.
