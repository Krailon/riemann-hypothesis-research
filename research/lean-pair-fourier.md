# Pair Fourier test-function passage

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
Ledger: `PAIR-TRANSLATION-FORMAL-001`, `PAIR-FOURIER-FORMAL-001`.
The exact translation uses no prime asymptotic or zero-free strip. Only the
integrated asymptotic inherits the pinned **PREPRINT** input through
`PAIR-ASYMPTOTIC-FORMAL-001`. Its total constants are existential.

## Observable and convention

Write W_T for the finite set of actual zero occurrences in **0 < gamma <= T**,
including analytic multiplicity, and put C_T=T log(T)/(2 pi), A_T=log(T)/(2 pi).
For continuous compactly supported g:R->C define

\[
 \widehat g(z)=\int_{\mathbb R}g(a)e^{-2\pi i z a}\,da,\qquad
 J_T[g]=\frac1{C_T}\sum_{i,j\in W_T}
 \frac{4\widehat g(iA_T(\rho_i-\rho_j))}{4-(\rho_i-\rho_j)^2}.
\]

`pairComplexFourier_real` identifies this with mathlib's Fourier transform on
real arguments. The existing two-dimensional `complexFourier` uses the positive
inverse sign; the new one-dimensional definition is deliberately distinct.
Compact support proves integrability for **every complex z**. All ordered pairs
are included. For T>=3 the exact identity is

\[
 J_T[g]=\int_{\mathbb R}g(a)\mathcal F_T(a)\,da.
\]

Only finite sums are interchanged with integrals. Every summand is integrable.
Full complex differences are retained: this is not an ordinate-only statistic.

## Complete translation bookkeeping

`PairFourierBookkeeping` expands the horizontal and vertical exponential and
rational denominator. The index diagonal contributes card(W_T); the equal-complex-
zero diagonal contributes the sum of m(rho)^2 over distinct zeros in the window.
A separate fiber-cardinality proof connects finite occurrence counts to the actual
analytic multiplicities. Equal ordinates are not substituted for equal zeros.
Reflection of the second occurrence reindexes the full sum via rho_j+conj(rho_k)-1.
It is not asserted to preserve diagonal subsets.

For **T>2 pi**, put L_T=log(T/(2 pi))/(2 pi), q_T=A_T/L_T, and
u=L_T(gamma_j-gamma_i). `PairFourierScaling` proves positivity and

\[
 C_T=q_T T L_T,\quad
 iA_T(\rho_i-\rho_j)=q_Tu+i(x_i-x_j)/(2\pi),\quad
 G_T(\xi)=q_T\mathcal F_T(\xi/q_T).
\]

Under xi=q_T a the vertical phase is exp(-2 pi i xi u), the closed support
interval |a|<=1 maps exactly to |xi|<=q_T, and dxi=q_T da. In particular

\[
 \int g(\xi/q_T)G_T(\xi)\,d\xi=q_T^2\int g(a)\mathcal F_T(a)\,da.
\]

The Jacobian and change of normalization each supply one factor q_T. The local
scale statements do not include T=2 pi; the source-scale statistic does include T=3.

## Integrated asymptotic and named errors

For q>0 the nonnegative kernel k_q(a)=q exp(-2q|a|) has exactly

\[
 \int k_q=1,\qquad \int |a|k_q(a)\,da=\frac1{2q}.
\]

Both integrals are proved integrable. The first-moment bound controls the peak
without interchanging an asymptotic limit and an integral. Fix a complex C^1 test
g with compact support in **[-1,1]**. This includes the planned smooth tests.
Global bounds M0>=sup|g| and M1>=sup|g'| exist by compact support; the mean value
theorem gives |g(a)-g(0)|<=M1|a|. There are absolute positive A,B, chosen before
all tests and heights, such that for T>=3,

\[
 \left|J_T[g]-g(0)-\int_{\mathbb R}|a|g(a)\,da\right|
 \le \frac{A M_0+M_1/2}{\log T}
       +\frac{B\int |g(a)|\,da}{\sqrt{\log T}}.
\]

| Error | Uniform bound |
| --- | --- |
| Integrated spectral peak remainder | A M0/log T |
| Approximate-identity peak error | M1/(2 log T) |
| Integrated mean-square remainder | B integral(|g|)/sqrt(log T) |

The first and third errors come from the uniform pair asymptotic, using g=0
outside the closed interval. The second is an exact kernel estimate. The total
is bounded by C_g/sqrt(log T), for a positive constant chosen after g and before T.
`pairFourier_tendsto` proves the corresponding Lean `Tendsto` statement:
**fix g first, then T tends to infinity**. No moving-test limit is asserted.
The endpoint inclusion follows from the already checked closed frequency bound;
there is no support-boundary density argument hidden here.

## Dependencies and verification

Definition-only interface: `PairFourierDefinitions`. Proof modules:
`PairFourierIdentity`, `PairFourierBookkeeping`, `PairFourierScaling`,
`PairFourierPeak`, `PairFourierAsymptotic`.

The exact branch uses actual occurrences, finite reflection and the realness of
Phi. The kernel branch uses elementary exponential/Gamma integrals, compact
support and the mean value theorem. The final branch adds the normalized pair
asymptotic. Every public theorem has an independent Comparator statement, an
inventory entry and an axiom report. Only `propext`, `Quot.sound`, and
`Classical.choice` are permitted; the external kernel is disabled. The unfinished
limit theorem is the negative control and must be rejected for `sorryAx`.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --pair-fourier-only
```

The focused suite includes the combined build, complete axiom report, coverage,
pair/triple regressions and harness regressions. Earlier Comparator suites are
not rerun. Successful content-addressed evidence is linked in the ledger.

Historical ledger statuses and audit scopes are preserved. The coverage map
records the exact `PAIR-TRANSLATION-001` statement as complete; effective total
asymptotic constants, classical KV-route inputs, explicit norm tails, triple
analytic formalization and the signed complex-argument triple o(1) problem remain
separate obligations. No new RH implication is claimed.
