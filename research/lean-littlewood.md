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

## Verification and provenance

The existing pinned and ported Zeta23 weighted argument principle is reused
without modifying vendored sources. Its axiom report is included explicitly, in
addition to all project declarations. Mathlib supplies analytic orders, real-path
calculus for complex functions, the fundamental theorem of calculus, finite-sum
inequalities, and elementary zeta analyticity/nonvanishing.

The suite contains 36 public statements in seven modules. Definition-only
Comparator contracts cover every statement. Eleven unfinished controls cover log
transport, integrability, contour orientation, the weighted argument principle,
the identity, count bounds, actual zeta specialization, constant functions,
repeated zeros, threshold exclusion and branch invariance. Checked examples give
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
Mollified-zeta order comparisons, mollifier and twisted second-moment estimates,
and the uniform density theorem remain further work. In particular, this lemma
does not instantiate `UniformDyadicDensity`, prove a close-pair bound, establish
a density-based moment estimate, or settle the signed complex-argument error.
Historical density and pair/triple theorem statuses remain unchanged.
