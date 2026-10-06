# Regenerated triple normalization and error accounting

Task: verification/exposition. `UNCONDITIONAL` with `SUPPORT(h<=1-kappa, 0<kappa<1)`.
Claim `TRIPLE-SMOOTHED-CORRELATION-001`, status `proved-draft`. No analytic proof certificate.

## Main-term assembly

Quadrant origin: `1/4`; quadrant ray: `3/4`.
Six sectors give origin `3/2`; shared rays each have two incidences.
Normalization factor: `2/3`; final origin: `1`.
Observable coefficient: `16/3 * T^(-1) * q^(-1)`.
Main functional: `phi(0,0)+integral |r|*(phi(r,0)+phi(0,r)+phi(r,-r)) dr`.

## Five occurrence partitions

| Pattern | Physical pairing | Fourier basis coefficients |
| --- | --- | --- |
| all_equal | `F(0,0)` | `{"planar_one": 1}` |
| 12_equal | `integral F(0,r)*(1-s(r)^2) dr` | `{"line_eta": 1, "triangle_eta": -1}` |
| 13_equal | `integral F(r,0)*(1-s(r)^2) dr` | `{"line_xi": 1, "triangle_xi": -1}` |
| 23_equal | `integral F(r,r)*(1-s(r)^2) dr` | `{"line_sum": 1, "triangle_sum": -1}` |
| all_distinct | `integral F(u,v)*R3(u,v) du dv` | `{"cycle_overlap": 2, "origin": 1, "triangle_on_line_eta": -1, "triangle_on_line_sum": -1, "triangle_on_line_xi": -1}` |

Fourier basis definitions and the exact sum are recorded in the JSON.

## Named errors

- `E_signed = phi_C1*(1+W_inf+W_1)*(b^(-1)+decay*L^3)`.
  After exact scaling: `2/3 * b^(-1) * phi_C1 + 2/3 * L^(3) * decay * phi_C1 + 2/3 * W_inf * b^(-1) * phi_C1 + 2/3 * L^(3) * W_inf * decay * phi_C1 + 2/3 * W_1 * b^(-1) * phi_C1 + 2/3 * L^(3) * W_1 * decay * phi_C1`.
- `E_kernel = phi_L1*(W_inf+Wprime_inf)*decay*L^3`.
  After exact scaling: `2/3 * L^(3) * W_inf * decay * phi_L1 + 2/3 * L^(3) * Wprime_inf * decay * phi_L1`.

Each inherited absolute bound is multiplied by 2/3 exactly. The final theorem absorbs this factor and the inherited effective unspecified constants into an unspecified absolute C; no numerical C is computed.

## Scope and limits

The full horizontal profile and complex arguments are retained; all ordered occurrence patterns are included.
Support: `max(|xi|,|eta|,|xi+eta|)<=1-kappa`, `0<kappa<1`; internal axes included, outer boundary excluded.
Remove independent zero cutoffs at fixed parameters; then fix test, margin and smoothing before T tends to infinity.
additive, including zero main terms; varying families must make both errors vanish.
Critical parameter specialization has finite-height factors `3b/(2q)` and `b/q`, with limits `3/2` and `1` respectively.
Kernel parameters delta=0 only; applying to every zero would require RH.

Definitions, conventions and source labels are supplied in the JSON. Analytic bounds remain inputs from the written proof.
