# Paired Mellin kernel, including the endpoint

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
This follows the [pair-series convergence milestone](lean-pair-series.md).
The new ledger claim is `PAIR-MELLIN-KERNEL-001`.

## Exact statement and orientation

For every real y>0, define

    G_y(t) = 2 exp((2+i t) log y) / ((2+i t)^2-1).

`pairedMellinUpwardIntegral` explicitly retains the Jacobian i of the
upward parametrization w=2+i t. Lean proves

    (1/(2 pi i)) integral_R G_y(t) i dt
      = (1/(2 pi)) integral_R G_y(t) dt
      = y-y^(-1) if y>1, and 0 if 0<y<=1.

The value at **y=1 is exactly zero**. There is no half-weight convention.
Positive real powers are exp(w log y); the bridge to mathlib's complex
power at the positive reciprocal 1/y is checked explicitly.

Both G_y and G_y*i are absolutely integrable. In particular the displayed
integrals are not assigned values by a principal-value convention. The
symmetric finite-height integrals over [-V,V], with the factor 1/(2 pi),
converge to the whole-line value as the real parameter V tends to infinity.

## Proof route

The proof uses pinned mathlib's Mellin inversion theorem. It recovers the
entire mathematical statement of `PAIR-EF-MELLIN-001`; the historical
contour-shift proof and its two-stage limit order are unchanged.

1. Define f(x)=x^(-1)-x on 0<x<=1, and zero elsewhere. For Re(s)>1,
   `hasMellin_cpow_Ioc` gives the two absolutely convergent transforms.
   Subtraction and exact field algebra give

       Mellin(f)(s) = 1/(s-1)-1/(s+1) = 2/(s^2-1).

   The seed may be singular near zero; its required **weighted** Mellin
   convergence is proved, rather than assuming unweighted integrability.

2. On the positive half-line, f(x)=max(x^(-1)-x,0). This identity proves
   continuity there, including x=1 where the two branches agree at zero.

3. On the vertical line, Lean proves

       |(2+i t)^2-1| >= 1+t^2,
       |exp((2+i t) log y)| = y^2,
       |G_y(t)| <= 2 y^2/(1+t^2).

   The first inequality follows from the exact squared norm
   t^4+10t^2+9. The integrable majorant proves absolute convergence,
   including y=1. At y=1 it also supplies vertical integrability of
   the rational Mellin transform required for inversion.

4. Apply `mellinInv_mellin_eq` on Re(s)=2 at x=1/y. All three premises
   are discharged: weighted Mellin convergence, vertical integrability,
   and continuity at the evaluation point. Explicit power and normalization
   bridges identify the inverse with the project kernel. Evaluating f(1/y)
   gives both branches and the endpoint.

5. Absolute integrability gives the symmetric finite-height limit via
   `intervalIntegral_tendsto_integral`. Here y>0 is fixed before V tends
   to infinity. No real-boundary shift, residue theorem, or second limit
   is part of this proof route.

The transform imports are from the pinned mathlib revision recorded in the
verification manifest: `Mathlib/Analysis/MellinTransform.lean` and
`Mathlib/Analysis/MellinInversion.lean`. The latter proves Mellin inversion
from Fourier inversion. Neither the new definitions nor the proof modules
import project zero-counting or zeta-strip theorems. No zeta hypothesis,
RH, numerical quadrature, or unproved contour estimate enters this lemma.

## Public interface and verification

The definition-only `PairedMellinDefinitions.lean` exports the seed, rational
symbol, line integrand, normalized kernel, upward integral and finite
truncation. `PairedMellinTransform.lean` proves the seed transform and
continuity; `PairedMellinBounds.lean` proves integrability, orientation and
cutoff convergence; `PairedMellin.lean` supplies inversion and the exact values.

The [inventory](lean-paired-mellin-inventory.json) lists **19 public
declarations**, each with a definition-only Comparator specification and
axiom report. The two imported transform/inversion theorems also have
explicit axiom reports. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted. The deliberately unfinished headline proof must be rejected
for `sorryAx`; solution modules never import the challenge placeholders.
No external-kernel check is claimed.

The full reproduction run on **2026-10-13 UTC passed**: **19 new Comparator
specifications**, **411 distinct axiom reports**, **ten unfinished-proof
controls**, **196 pair/triple regressions**, and **18 coverage checks**.
The [verification archive](../artifacts/certificates/lean/13c3955a3fe1b1df357984c779e493744ecb2f77030153f7b80a97a27f97e256/manifest.json)
contains command logs, source and tool hashes, dependency pins and compatibility
patches. This run used the existing project build cache; all new proof modules
had been compiled in this milestone, and every Comparator challenge was rerun.
No fresh-project or external-kernel run is claimed for this archive.

Reproduce with:

```bash
python3 -B scripts/reproduce_lean.py --skip-bootstrap
```

Add `--fresh-project` to rebuild the complete project from an empty project
build directory. Pinned dependency caches remain reusable.

The coverage map keeps the historical contour proof distinct from this
formalized inversion proof. Earlier ledger entries and historical audit
verdicts retain their original scope. Audit input hashes are refreshed in
order: ledger, pair audit, then the triple audit's reference to the pair audit.

## Next input

Formalize the exact pair explicit-formula identity, with its logarithmic
zeta derivative, pole term and trivial-zero series. The paired Mellin
identity now supplies the right-line kernel evaluation, including X=n.

This next input was completed in the [exact pair formula milestone](lean-pair-exact.md).
