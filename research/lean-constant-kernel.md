# Constant-kernel replacement: pointwise, project-scaled and summed

Assumptions: `UNCONDITIONAL`. The pointwise component and its project-scaled and summed extensions are
formalized below. Density-based vanishing remains a separate obligation.

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

## Project scaling and uniform Fourier decay

For q=log T, b=log(T/(2π)), ell=b/(2π), use
r=max(|ell a|,|ell d|) and x=q max_j |δ_j|, with anchor-first δ.
The checked q≤4π ell comparison gives, for T≥2π exp(2π),

    ||J_empty-J*|| ≤ C_scale (r²+x²)/q²,
    C_scale = 4096π(32π²+3).

`replacementP24` is exactly the sum of L1 norms of mixed coordinate partials
D_x^i D_y^j φ with i+j≤24, each multi-index counted once. The pure derivatives
needed by coordinate integration by parts are explicitly bounded by this sum.
The Fourier phase uses +2πi, and the checked integration-by-parts identity has
multiplier -2πi u_j. No change to the project Fourier units is made.

The tuple integral H is the inverse transform of φ times the product of the
three coshes minus one. Its finite sign expansion is an average of
exp(L)-1-L: the linear terms cancel exactly. For every derivative through
order 22, the exponential remainder keeps an x² factor. Hexagonal support
h≤s gives ||L||≤2sx, including tests crossing axes. For any smooth compact
complex φ with h≤s, 0<s<1, and T≥2π exp(1),

    |H| ≤ C_decay P24(φ) x²(1+x)^22 exp(2sx)/(1+r)^22,
    C_decay = 2^22 · 2^22 · 23 · 2^24 = 23 · 2^68.

The coefficient is intentionally loose but explicit, independent of the test,
height, smoothing and s. The argument needs no reality or symmetry of φ.

## Infinite sums and normalization

`replacementMoment` is the manuscript's

    M24,T(s) = (1/(Tq)) Σ_v ω(γ(v0)/T) x²(1+x)^24 exp(2sx)/(1+r)^20.

All indices are actual zero occurrences, with multiplicities, both ordinate
signs, and every ordered diagonal included. Only the anchor is localized.
At each fixed T≥2π exp(1), x≤q/2 bounds the horizontal factors. Existing
occurrence-shell counts prove absolute convergence of this moment, the
weighted H series, and the even, constant and replacement error series.
The Fourier integral is evaluated for each tuple before the zero sum.
No infinite zero-sum/Fourier-integral interchange is used.

With coefficient c_T=16/(3Tq), the exact identity is
E_even=E_constant+E_replacement. Independent finite cutoffs in the three slots
converge to all three normalized sums. Multiplying the scaled kernel estimate
by the tuple decay and absorbing two powers of gap decay gives, for
T≥2π exp(2π),

    |E_replacement| ≤ C_sum P24(φ) M24,T(s)/q²,
    C_sum = (16/3) C_scale C_decay.

The three constants displayed here are explicit. The shell-count constants
used only to establish summability may remain existential. Zero test, zero
horizontal displacement, equal ordinates, both height thresholds and the
exact normalization c_T J*=2π/(Tq) have checked specializations. The original
pointwise/scaled statements retain the closed horizontal cube; actual strip
zero displacements satisfy its bounds strictly.

## Reproduction and boundary

The combined suite has 68 public statements in 14 modules and 17 unfinished-
proof rejection controls. Expected contracts import definition-only modules.
Only `propext`, `Quot.sound` and `Classical.choice` are permitted; nanoda is
disabled.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --constant-kernel-only
```

The focused run checks the Comparator contracts and parallel rejection
controls, combined project build, complete axiom report, coverage and the
harness and pair/triple regressions. The successful certificate is recorded
in the appended formal ledger entry.

`ORDINATE-CONSTANT-KERNEL-001` remains partially formalized. The density-based
estimate and its strict-support vanishing consequence, and identification of
E_constant with the unaveraged signed full-zero statistic, remain separate.
The kernel-free signed complex-argument error tending to zero remains an
open research problem. No ordinate-only asymptotic follows from this milestone.
