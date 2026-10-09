# Lean milestone 4A: summability, limits, and integration

Task: formal verification and dependency bookkeeping. Assumptions:
`UNCONDITIONAL` for the explicitly quantified implications below. The count,
decay, integrability, and domination hypotheses are visible in the Lean
statements. They have not yet been discharged for the actual zeta observable.

**Verified:** the fresh-project run started on 2026-10-08 UTC passed
all **51 new Comparator declarations**, all earlier proof checks, four
unfinished-proof negative controls, **111 distinct axiom reports**,
**196 pair/triple regressions**, and **8 coverage-map checks**.
The [complete verification archive](../artifacts/certificates/lean/1dc056c83e0d8116fd8a7aaa08f74e75f4da7f1a9ed90932ac9ce009998ef457/manifest.json)
records exact source hashes, tool pins, logs and dependency changes.

The subsequent [actual-occurrence milestone](lean-actual-occurrences.md)
constructs actual zeta occurrences and discharges the fixed-height counting
and complex Fourier-decay hypotheses. The archived counts and outstanding
application work described below record the state at milestone 4A; consult
the current coverage map for the remaining obligations.

## Shell summability and a quantitative tail

`OccurrenceShells I` supplies a map $s:I\to\mathbb N$, finite sets $D_n$,
and the exact membership equivalence $i\in D_n\iff s(i)=n$. Thus the shells
are disjoint and cover every occurrence, including repeated values carried
by different indices. No enumeration of actual zeta zeros is assumed.

For $f:I\to\mathbb C$, nonnegative $A,C$, and natural numbers $d<p$, assume
\[
 |D_n|\le C(2^d)^n,\qquad
 \lVert f(i)\rVert\le A/(2^p)^{s(i)}.
\]
Put $\theta=2^d/2^p$. Then $0\le\theta<1$, and summing over a finite shell gives
\[
 \sum_{i\in D_n}\lVert f(i)\rVert\le AC\theta^n.
\]
The convergent geometric majorant and the partition of occurrences imply
absolute summability. Regrouping the nonnegative tail by shells, and shifting
$n$ by $N$, gives the checked bound
\[
 \boxed{\sum_{s(i)\ge N}\lVert f(i)\rVert
       \le AC\frac{\theta^N}{1-\theta}.}
\]
The tail includes shell $N$. The formula also covers $N=0$, empty shells,
and vanishing constants. The original complex series is summable as a
consequence of norm summability.

For a radius $r_i$ satisfying $2^{s(i)}\le1+r_i$, the pointwise bound
$\lVert f(i)\rVert\le A(1+r_i)^{-p}$ implies the required shell decay.
The project choices $(d,p)=(4,20),(4,22)$ give ratios $1/65536$ and
$1/262144$, respectively. Counting constants and decay constants may depend
on fixed height and test data: these theorems do not make them uniform in $T$.
Constructing the actual dyadic shells and deriving their counts are separate
application obligations. In particular, a weighted counting estimate alone
is not silently substituted for an unweighted shell-cardinality bound.

The proof uses mathlib's nonnegative partition criterion, norm comparison,
`HasSum.tsum_fiberwise`, and the geometric-series theorem at the existing pin.
All zero-sum rearrangements here follow established absolute summability.

## Cutoffs, fibers, patterns, and reflection

`occurrence_cutoff_limit` applies to a function with summable norms in any
complete normed additive group. For finite occurrence sets $S_k$ indexed by
an arbitrary filter, the hypothesis is that each occurrence eventually
belongs to $S_k$. Every fixed finite set is consequently eventually contained
in $S_k$; composing the defining finite-set sum limit proves cutoff removal.
Monotonicity of the family is sufficient but is not required.

For triples the cutoffs are the existing full Cartesian domains
`tripleDomain S`. The formal results cover both:

- the net over three finite sets ordered by componentwise inclusion;
- three separately exhausting sequences, indexed by
  $N\in\mathbb N^3$ with componentwise `atTop`.

No relation between the three cutoff growth rates is required. All ordered
triples and index coincidences remain included.

The infinite regrouping identity uses occurrence subtypes $\{i:q(i)=a\}$,
not a set of distinct zero values. When every fiber is supplied as a finite
set with that exact membership equivalence, a fiber-constant summand acquires
its full cardinality factor. Regrouping by `classifyTriple` gives exactly the
five ordinate-equality patterns from milestone 2.

An explicit occurrence involution induces a bijection on each reflected
triple domain. Its infinite reindexing preserves summability and the sum.
To reindex within one ordinate-pattern class, the involution must preserve
the ordinate label. This gives the eight-reflection identity both for the
full sum and for each ordinate class. It does not assert preservation of
index-equality patterns by independent slot reflections.

`dominated_occurrence_limit` is a project interface to mathlib's Tannery
theorem: termwise convergence plus an eventually uniform summable norm
majorant allows the sum and parameter limit to commute. Its majorant is an
explicit hypothesis, never inferred from fixed-parameter convergence.

## Evaluated integrals and absolute interchange

These are two separate operations with separate checked interfaces.

| Operation | Required control | Conclusion |
| --- | --- | --- |
| Sum already evaluated integrals | Each $G_i$ is integrable; a summable $B_i$ bounds $\lVert\int G_i\rVert$ | Absolute summability of the evaluated integrals and removal of occurrence cutoffs |
| Interchange the infinite sum and integral | Countably many integrable $G_i$ and $\sum_i\int\lVert G_i\rVert<\infty$ | $\sum_i\int G_i=\int\sum_iG_i$, including the limit of integrals of finite cutoff sums |
| Pass a parameter limit under an integral | Almost-everywhere convergence, measurable terms, and one integrable dominating function | Convergence of the integrals |

The first interface supplies no proof of the stronger hypothesis in the
second row. This distinction matches the kernel-free representation in
`ORDINATE-CONSTANT-KERNEL-001`, which first evaluates each Fourier integral.
The actual compact-Fourier integration-by-parts estimate is not formalized
in this tranche.

## Integrated horizontal-square inequality

Retain the finite definitions from milestone 3:
\[
 m_D=|D|,\quad Q_D=\sum_{i\in D}\delta_i^2,\quad
 P(\xi,\eta)=\xi^2+\xi\eta+\eta^2,
\]
\[
 B_D(b,\xi,\eta)=\sum_{i,j,k\in D}
 \bigl[\cosh(b\delta_i(\xi+\eta))\cosh(b\delta_j\xi)
              \cosh(b\delta_k\eta)-1\bigr].
\]
For a continuous compactly supported real function $\phi$ on $\mathbb R^2$,
both $\phi B_D$ and $\phi P$ are integrable: the finite cosh sum and polynomial
are continuous, and multiplication retains compact support. Integrals use
Lebesgue measure on $\mathbb R\times\mathbb R$.

If additionally $\phi\ge0$, integration of the already verified pointwise
inequality gives
\[
 \boxed{\int\phi B_D\ge b^2m_D^2Q_D\int\phi P\ge0.}
\]
The hypotheses allow all real $b,\delta_i$ and every compact Fourier support;
there is no excluded frequency axis or origin and no small-displacement
assumption. Nonnegativity of $\phi$ is essential to this comparison.

For a countable family of finite sets $D_g$ with weights $W_g\ge0$, put
$E_g=W_g\int\phi B_{D_g}$ and
$L_g=W_gb^2m_{D_g}^2Q_{D_g}\int\phi P$. The theorem assumes
$\sum_g E_g$ is summable, derives summability of $L_g$ from
$0\le L_g\le E_g$, and proves
\[
 \sum_g L_g\le\sum_g E_g.
\]
This is a theorem about a supplied family of finite sets. Identifying them
with disjoint, exhaustive actual zero fibers is an additional application
step. It does not assert convergence of an integral of the full infinite
family. Nor does it infer summability of unweighted square masses when
$b$ or $\int\phi P$ vanishes.

## Formal declarations and examples

| Module | Role | New declarations |
| --- | --- | ---: |
| `OccurrenceSummability` | Shell comparison, summability, explicit tail, radius conversion | 11 |
| `OccurrenceLimits` | Independent cutoffs, fibers, five patterns, reflection, dominated sum limit | 12 |
| `OccurrenceIntegration` | Two integral interfaces, dominated integral limit, integrated square bound | 13 |
| `SummabilityExamples` | Exact boundary, multiplicity, and limit-obstruction checks | 15 |

The examples cover an exact geometric tail, a singleton-shell series,
repeated labels, empty occurrence types, reflection fixed points, independently
growing cutoffs, empty integrated fibers, zero scale, and zero test weight.
The endpoint example records $\theta=1$ at $p=d$ and non-summability of a
nonzero constant series. Existing milestone-3 checks retain frequency axes,
the origin, and the anti-diagonal.

The moving-singleton family $f_n(i)=1_{i=n}$ is summable for each $n$ and
converges to zero at each fixed $i$, but every row sum is one. Lean verifies
both facts and proves that no summable norm majorant can dominate all rows.
Thus pointwise convergence alone cannot justify the desired limit interchange.
These are exact abstract examples, not experiments about actual zero locations.

## Working backwards through the analytic graph

The [coverage map](lean-analytic-coverage.json) follows the ledger closures
of the weighted triple theorem, constant-kernel lemma, and open ordinate-only
target. It contains **46 nodes and 92 edges**. Its `root_to_inputs_order`
visits each dependent before its prerequisites; the historical dependency
edges are preserved verbatim. Its component inventory binds all 51 new
declarations to their source modules and Comparator configuration.

| Layer to inspect | Formal coverage from this tranche | Remaining application work |
| --- | --- | --- |
| Weighted and ordinate-only statements | Abstract cutoff and dominated-limit tools | Main term, error asymptotics, and the open signed cancellation estimate |
| Transfer and constant-kernel representation | Absolute-sum cutoffs and evaluated-integral summation | Actual occurrence model, tuple decay, and exact complex-test identification |
| Sign averaging | Infinite occurrence reindexing and five ordinate classes | Multiplicity-preserving zeta involution and the Fourier-integral majorant |
| Kernel and Fourier analysis | Dominated integral limits and integrated finite positivity | Rational-kernel estimates, residues, derivative bounds, compact-Fourier integration by parts |
| Zero counting and explicit formula | Shell summability conditional on counts and decay | Inclusive local counts, shell construction, contour and archimedean estimates |
| Prime-side estimates | No new formal coverage | PNT, sieve, mean-value bounds and the recorded prime combinatorics |

The map marks partial coverage without changing any historical theorem
status. In particular, neither the triple theorem nor the constant-kernel
lemma becomes fully formalized because it can use these generic tools.
The open argument-vanishing and ordinate-only claims remain `idea` in the
ledger and `open_research` in the map.

**Next small step:** construct the multiplicity-preserving zero-occurrence
interface and finite height cutoffs. Then discharge the counting and
bounded-imaginary-strip Fourier-decay hypotheses for the transfer identity.
The map records every remaining prerequisite; it is not an analytic proof
certificate or an independent RH audit.

## Reproduction and limit order

```bash
python3 -B scripts/reproduce_lean.py --fresh-project
python3 -B scripts/check_lean_analytic_coverage.py
```

Existing installations may add `--skip-bootstrap`. The definition-only
challenge imports `SummabilityDefinitions`; solutions never import the
challenge or its intentional unfinished proofs. The harness checks all new
public declarations, rejects an unfinished control, retains previous checks,
and restricts axioms to `propext`, `Quot.sound`, and `Classical.choice`.
The optional external kernel remains disabled, as in the earlier milestones.

First fix height, test, smoothing, and support margin, and remove occurrence
cutoffs under the proved hypotheses. A later height limit requires its own
uniform domination or error argument. This tranche supplies no such
zeta-specific height bound and does not prove the remaining signed $o(1)$.
