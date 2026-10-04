# Recorded failed proof routes

## Ordinate transfer at microscopic horizontal distance

Date: 2026-10-03. Task: proof diagnosis. Assumptions: `UNCONDITIONAL` for the
identified gap; `SYNTHETIC_MODEL` for the finite sensitivity example.

**Attempt.** Deduce replacement of complex test arguments by real ordinate
arguments from the smallness of unscaled `delta=beta-1/2` for most zeros.

**Obstruction.** The arguments depend on `L_T(delta_j+delta_1)`. Control of
`delta=o(1)` gives no control tending to zero at this scale. The density
cutoff `64 log log T/log T` that suffices for the real-test kernel leaves
imaginary shifts of size `O(log log T)`. The current density bound also
permits a nonvanishing proportion at displacement `c/log T`.

**Smallest local sensitivity fixture.** A symmetric quartet at displacements
`+/-c/log T` and ordinates `+/-gamma` respects all required zero symmetries.
At the positive ordinate the eight ordered sign choices multiply a Fourier
mode in the limit by `cosh(c xi) cosh(c eta) cosh(c(xi+eta))`, which need not
equal one. A finite quartet has vanishing normalized mass; this is only a
counterexample to the pointwise continuity inference, not to a zeta theorem.

**Type.** Structural scale mismatch in this inference; it is not a barrier
theorem for other methods or for signed cancellation.

**Repair.** Establish the signed `E_arguments=o(1)` estimate in the
[reduction](triple-ordinate-reduction.md), prove its sufficient weighted
microscopic moment tends to zero, or construct a different direct
ordinate-only explicit-formula argument.

## Reflection alone cancels only the odd horizontal contributions

Date: 2026-10-03. Task: proof diagnosis. Assumptions: `UNCONDITIONAL` for
the exact decomposition; `SYNTHETIC_MODEL` for the quartet fixture above.

**Attempt.** Obtain the missing signed cancellation by independently
reflecting all three occurrences and discarding odd terms.

**Obstruction.** The eight-reflection identity retains
`J_empty (prod cosh(a_j)-1)`. Its quadratic term contains the horizontal
squares multiplying second derivatives of F. The quartet already recorded
above gives a nonzero even mode multiplier. Reflection has no further sign
with which to cancel it. Positivity of this frequency multiplier also does
not imply positivity after pairing with vertical phases and a general test.
Independent reflections act on the full Cartesian product, not separately
on each equality pattern of indices.

**Type.** An algebraic limit of this symmetry argument, not a theorem that
the full zeta sum cannot cancel across ordinates or frequencies.

**Repair.** The new kernel-mixing estimate removes that term on fixed
`h<=s<331/4000`. What remains is a signed weighted correlation estimate for
`E_even`, or horizontal concentration strong enough to make its sufficient
moment small. The current density bound does neither. No finite synthetic
configuration is presented as a counterexample to a normalized zeta limit.
