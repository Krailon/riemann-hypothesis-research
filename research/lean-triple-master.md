# Triple master interchange and exact kernel identity

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
Ledger: `MASTER-INTEGRATION-FORMAL-001` and `MASTER-IDENTITY-FORMAL-001`.
These milestones discharge integral-norm summability and the exact kernel identity in
`TRIPLE-MASTER-001`. Its whole statement remains partially formalized.

## Checked statement

Use the existing actual-zero term S_i(X,t)=`pairZeroTerm i (X,t)`.
Every i is a zero occurrence with analytic multiplicity; both ordinate signs
and all ordered triples are included. For T>=3, X,Y>=1, define

\[
 G_v(t)=\frac{\omega(t/T)}T S_{v_0}(X,t)S_{v_1}(Y,t)
           \overline{S_{v_2}(XY,t)},\qquad v:\{0,1,2\}\to\mathcal I.
\]

The smoothing weight omega is any **continuous real function supported in
[1,2]**. Positivity, smoothness and unit mass are unnecessary for this bound;
the manuscript's nonnegative smooth probability weights are included.

There exists C0>0, chosen before every smoothing weight and every parameter,
such that Q(t)=sum_i (1+(t-gamma_i)^2)^(-1)<=C0 log(|t|+2) and

\[
 \sum_v\int_{\mathbb R}|G_v(t)|\,dt
 \le (8/3)^3 C_0^3XY\log^3(2T+2)\int_{\mathbb R}|\omega(u)|\,du <\infty.
\]

`tripleMaster_uniform_integralNorm` proves summability and this bound together.
The explicit factor (8/3)^3 is preserved. C0 is the existing existential zero-
kernel constant; no numerical effectivity upgrade is asserted. For a specified
C0 satisfying the zero-kernel estimate, `tripleMaster_integralNorm_bound`
provides the same conclusion directly.

`tripleMaster_sum_integral` then proves

\[
 \sum_v\int G_v(t)\,dt=\int\sum_vG_v(t)\,dt.
\]

The evaluated-integral series is absolutely convergent as a consequence of the
stronger sum of integral norms. Pointwise absolute summability is also checked.

## Exact kernel identity

`tripleMasterObservable` is the integral of the full-series product
omega(t/T)/T * S(X,t) S(Y,t) conjugate(S(XY,t)). Write

\[
 D_i(t)=1+(t-\gamma_i+i(\beta_i-\tfrac12))^2,\qquad
 K_T(v)=\frac1T\int_{\mathbb R}
 \frac{\omega(t/T)}{D_{v_0}(t)D_{v_1}(t)\overline{D_{v_2}(t)}}\,dt.
\]

`tripleMaster_kernel_identity` proves

\[
 C_{3,T}(X,Y)=8\sum_v
 X^{\rho_{v_0}+\overline{\rho_{v_2}}-1}
 Y^{\rho_{v_1}+\overline{\rho_{v_2}}-1}K_T(v).
\]

Positive-real powers mean exp(log(base) * exponent). `tripleMasterKernel`
is the smoothed absolute-center kernel, not the unweighted `integralProfile`.
`tripleMasterKernel_normalization` moves its exact factor 1/T outside the
integral. The coefficient retains horizontal **sums** delta_0+delta_2 and
delta_1+delta_2 and ordinate differences gamma_0-gamma_2 and gamma_1-gamma_2.

The proof first factors finite rectangular sums, then uses absolute convergence
and uniqueness of the cutoff limit to identify the full-series product.
`tripleMaster_phase_cancel` cancels the t-dependent exponents using
log(XY)=log(X)+log(Y). Each term is eight times its constant coefficient times
the kernel integrand. Integral linearity and the previously proved interchange
then give the displayed identity. `tripleMaster_kernel_norm_summable` proves
absolute convergence of the explicit coefficient-times-kernel series.

The kernel and full-product integrands are separately proved integrable. Kernel
integrability also follows from the X=Y=1 term identity, with its nonzero factor
8. The denominator is nonzero throughout the full critical strip, including
coincident ordinates and repeated occurrence indices. No distinctness condition
or RH assumption enters any statement. Named observable cutoff theorems now
identify the limits of the finite products with C_{3,T}. T=3, X=Y=1 and zero/
negated weights have explicit checked specializations.

## Proof dependencies and domination

The proof uses `pairZeroTerm_bound` and `zeroKernel_summable_bound`. The former
bounds each S_i by (8/3)sqrt(X)/(1+(t-gamma_i)^2), using only the full critical
strip |beta-1/2|<=1/2. The three square roots multiply to XY because Z=XY.
No critical-line substitution or narrower zero-free strip is used.

For any finite set D of occurrence triples, the sum of the three-factor
nonnegative rational kernels is bounded by Q(t)^3. The proof encloses D in the
Cartesian cube of its finitely many slot values, factors the finite sum, and
uses the already checked summability of the single kernel.

This yields the explicit common dominating function

\[
 B(t)=(8/3)^3C_0^3XY\log^3(2T+2)\frac{|\omega(t/T)|}{T}.
\]

The support is contained in [T,2T]. Continuity and compact support prove each
G_v and B integrable; change of variables proves integral(B) equals the displayed
bound. Finite sum/integral linearity bounds every finite sum of integral norms.
The nonnegative-series criterion `summable_of_sum_le` then establishes the
required infinite summability. Finally the existing `integral_occurrence_sum`
interface applies with its hypotheses fully discharged. This argument does not
assume the infinite interchange in order to prove it.

## Cutoff and endpoint conventions

Fix **T,X,Y,omega first**. `tripleMaster_independent_cutoff_limit` allows the
three finite occurrence sets to exhaust independently. The corresponding
integrated finite sums converge to the integral of the infinite triple sum.
`tripleMaster_height_cutoff_limit` specializes this to independent real
heights U_0,U_1,U_2 with the inclusive cutoff **|gamma|<=U_r**. Multiplicities
at an endpoint are retained in full. The product filter also permits taking all
three cutoffs along a cofinal joint path; there is no prescribed iterated order.

T=3 and X=Y=1 are included literally and have an explicit theorem instance.
The zero-weight and negated-weight identities are checked. The support hypothesis
uses a closed interval, so there is no omitted endpoint argument. No asymptotic
in T, changing smoothing weight, or uniform cutoff convergence in varying T is
claimed.

## Verification and remaining boundary

Definition-only interface: `TripleMasterDefinitions`. Proofs:
`TripleMasterBounds`, `TripleMasterIntegration` and `TripleMasterIdentity`.
All **39 public declarations** have independent Comparator statements, inventory
entries and axiom reports. The unfinished uniform integral-norm bound and headline kernel identity must be
rejected for `sorryAx`. Only `propext`, `Quot.sound` and `Classical.choice` are
permitted; the external kernel is disabled.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-master-only
```

The focused mode checks the new Comparator suite, negative control, combined
project build, complete axiom report, analytic coverage and pair/triple/harness
regressions. Earlier Comparator suites are not rerun. The ledger links the
successful content-addressed evidence.

The proof uses the existing unconditional counting/convergence infrastructure,
not the imported PREPRINT fixed strip. The next step is the five-pattern decomposition of the now identified
absolutely convergent kernel series. The five-pattern decomposition,
27-word expansion, prime resonance and Fourier-decay clauses remain separate
formalization tasks. Historical claim statuses and pair/triple audit scopes are
preserved; the open signed complex-argument triple error is unaffected.
