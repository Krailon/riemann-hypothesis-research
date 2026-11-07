# Pointwise constant-kernel replacement

Assumptions: `UNCONDITIONAL`. This milestone covers only the first inequality
of `ORDINATE-CONSTANT-KERNEL-001`, not its scaled or summed consequences.

The public theorem `HigherCorrelations.constantKernelEmpty_pointwise` states,
for all real a,d and every δ : Fin 3 → ℝ with |δ j| ≤ 1/2,

    ||J_empty(a,d;δ) - 3π/8|| ≤ 4096π min(a²+d²+Σⱼ δⱼ², 1).

`constantKernelEmpty` is exactly the empty coefficient of the existing
`signCoefficient`: 1/8 times all eight independent horizontal reflections.
The coordinate convention is anchor first. The rational profile receives
(δ₁,δ₂,δ₀), with positive imaginary anchor center and negative imaginary
non-anchor centers. The checked expanded profile identity makes this explicit.
This is an identity of kernels for arbitrary parameters; it does not regroup
any zero subseries or assume independent reflections preserve index diagonals.

Pairing each sign vector with its opposite cancels the first horizontal
Taylor term. The existing uniform second derivative bound, together with
(Σ|δⱼ|)² ≤ 3Σδⱼ², gives

    ||J_empty - J_zero-horizontal|| ≤ 3072π Σⱼ δⱼ².

For a²+d² ≤ 1, the checked critical-parameter quadratic expansion with radius
sqrt(a²+d²) gives

    ||J_zero-horizontal - 3π/8|| ≤ 4π(a²+d²).

The global bound ||J_empty|| ≤ 7π/9 then supplies saturation at 1. The chosen
4096π is explicit and deliberately nonoptimal; no inherited existential
constant is needed for this pointwise component. All real gaps are allowed.
The origin, coincident gaps and all eight corners of the closed horizontal
cube have separate checked specializations. The main theorem itself includes
all faces, edges, and the energy threshold 1.

## Reproduction and boundary

Nine public statements in three modules have definition-only expected
contracts. Seven rejection controls cover profile conventions, horizontal
and real-gap bounds, the assembled estimate, origin, coincidence and cube
endpoints. Only `propext`, `Quot.sound` and `Classical.choice` are permitted;
nanoda is disabled.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --constant-kernel-only
```

The focused run checks the Comparator contracts and parallel rejection
controls, combined project build, complete axiom report, coverage and the
harness and pair/triple regressions. The successful certificate is recorded
in the appended formal ledger entry.

The historical constant-kernel lemma remains partially formalized. Its
project-scaled estimate, absolute convergence and exact splitting identities,
summed replacement budget and density-based vanishing remain separate.
The kernel-free signed complex-argument error tending to zero remains an
open research problem. No ordinate-only asymptotic follows from this milestone.
