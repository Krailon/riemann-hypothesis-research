# Triple master integral-norm bound and interchange

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
Ledger: `MASTER-INTEGRATION-FORMAL-001`.
This milestone discharges the integral-norm summability obligation in
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
`TripleMasterBounds` and `TripleMasterIntegration`.
All **23 public declarations** have independent Comparator statements, inventory
entries and axiom reports. The unfinished uniform integral-norm bound must be
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
not the imported PREPRINT fixed strip. The next step is to identify the summed
integrand with the product of full zero series and cancel its center phases to
obtain the manuscript's explicit K_T identity. The five-pattern decomposition,
27-word expansion, prime resonance and Fourier-decay clauses remain separate
formalization tasks. Historical claim statuses and pair/triple audit scopes are
preserved; the open signed complex-argument triple error is unaffected.
