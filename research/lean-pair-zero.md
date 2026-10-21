# Exact pair zero-side decomposition

Task: formal verification. Assumptions: `UNCONDITIONAL`.
Ledger entry: `PAIR-ZERO-DECOMPOSITION-FORMAL-001`.

## Checked statement

For real X>=1 and T,Z>=0, using actual nontrivial zero occurrences with
analytic multiplicity, the exact identity is

```
L(X,T) = 2*pi*Re Phi(X,T) + E_trunc(X,T,Z) + E_height(X,T,Z) + E_extension(X,T).
```

Here L is the existing `pairZeroMeanSquare`, with its normalization unchanged.
The independently defined complex pair sum is

```
Phi(X,T) = sum_{i,j : 0<gamma<=T} exp(log(X)*(rho_i-rho_j))*4/(4-(rho_i-rho_j)^2).
```

All ordered pairs are included: repeated indices, repeated complex zeros,
and distinct complex zeros sharing an ordinate. The finite squared-norm
identity proves that Phi is real and nonnegative; taking its real part in the
real-valued decomposition does not discard an unproved imaginary contribution.

Put

```
v_i(t) = exp(log(X)*(delta_i+i*gamma_i)) / (1+((t-gamma_i)+i*delta_i)^2),
U(t) = sum_i v_i(t),
U_Z(t) = sum_{|gamma_i|<=Z} v_i(t),
V(t) = sum_{0<gamma_i<=T} v_i(t).
```

The errors are defined by the manuscript integrals, independently of the theorem:

```
E_trunc     =  4*integral_0^T (|U|^2-|U_Z|^2),
E_height    =  4*integral_0^T (|U_Z|^2-|V|^2),
E_extension = -4*integral_{R outside [0,T]} |V|^2 <= 0.
```

No condition Z>=2T is needed for this identity. The manuscript-range wrapper
has X>=1,T>=3,Z>=2T. The full sum retains possible ordinate-zero occurrences;
the positive window excludes them, so no real-zero-exclusion premise is used.
Full weights are retained at gamma=T and gamma=+/-Z. Removing endpoints when
splitting Lebesgue integrals is justified by their measure zero and does not
alter the weights of zero occurrences.

## Proof and dependency order

1. **Two-factor integral.** On |e|,|f|<=3/4, prove absolute integrability and
   `integral scalarKernel(t-a,e)*scalarKernel(t,f) = 2*pi/(4+(a+i*(f-e))^2)`.
   For a!=0 use the existing finite simple-pole truncation theorem and new
   four-pole algebra. Extend to a=0 by dominated continuity, with the explicit
   integrable majorant `16/(1+t^2)`. The coincident-center value is pi/2.
   Individual simple poles are integrated on finite intervals only.
2. **Phase and convergence.** Existing absolute zero-series convergence implies
   absolute convergence of U. Prove `S=2*exp(-i*t*log X)*U`, a phase of modulus
   one, hence `L=4*integral_0^T |U|^2`. Continuity supplies interval integrability.
3. **Finite squared norm.** Every `v_i*conj(v_j)` is integrable by the two-factor
   result and real translation. Expand only the finite V sum. The pair integral
   involves `rho_i+conj(rho_j)-1`. The existing multiplicity-preserving reflection
   `rho_j -> 1-conj(rho_j)` preserves membership in (0,T] and converts this to
   `rho_i-rho_j`. Thus `Phi=(2/pi)*integral_R |V|^2` for every X>0 and real T.
4. **Exact decomposition.** Split the integrable |V|^2 over [0,T] and its complement,
   identify the interval integral, and telescope the three named differences.
   The extension sign follows from the nonnegative squared integrand.

Parameters X,T,Z are fixed throughout. The pole-radius limit is taken with its
parameters fixed; continuity at a=0 uses its stated common majorant. There is no
infinite double-zero expansion, infinite-sum/integral interchange, or height limit
in the decomposition. Actual displacements are bounded using the strip predicate
|delta|<=1/2; no quantitative zero-free region or RH assumption is required.

## Verification

`research/lean-pair-zero-inventory.json` records all 43 public declarations.
The Comparator challenge imports only `PairZeroDefinitions`; it does not import
the solution modules. It compares the algebraic and analytic helper statements,
finite norm identity, phase bridge, integrability, exact decomposition, extension
sign, X=1 specialization, zero-height and empty-window endpoints. The coincident
kernel theorem covers the repeated-pole case explicitly; finite norm statements
include 0<X<1. All public declarations and the set-integral splitting input have
axiom reports. An intentionally unfinished decomposition must fail for `sorryAx`.

On prepared dependencies:

```bash
python3 -B scripts/reproduce_lean.py --skip-bootstrap --pair-zero-only
```

The focused run checks this Comparator suite, unfinished-proof rejection, the
combined project build, the complete axiom report, coverage checks, and pair/triple
regressions. It archives actual dependency patches, source/tool hashes and logs.
Earlier Comparator suites are not rerun in this mode; the default runner includes
all suites. The allowed axioms remain propext, Classical.choice and Quot.sound.
NanoDa is disabled; no independent-kernel or clean-checkout claim is made.
The content-addressed successful manifest is referenced by the ledger entry.

## Remaining obligations

This formalizes the exact part of `PAIR-TRUNC-001`, not its quantitative estimates.
Next: bound E_trunc, E_height and E_extension uniformly, then absorb the losses
and assemble the normalized pair theorem. The explicit 512/27 norm-tail constant,
the historical one-complex-parameter integral's full strip and semicircle estimate,
and the finite-height envelope remain separate recorded obligations. Historical
norm/truncation claims retain partial coverage. The signed complex-argument triple
error remains open.

## Follow-up

The [uniform error-bound milestone](lean-pair-zero-bounds.md) now formalizes
all three named errors and the finite horizontal envelope. The scope above
records the earlier exact-identity milestone; cutoff optimization remains separate.
