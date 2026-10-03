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
