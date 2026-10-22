# Normalized pair asymptotic

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
Ledger: `PAIR-ASYMPTOTIC-FORMAL-001`. The comparison inherits the pinned OpenAI
**PREPRINT** input through `PAIR-ZERO-COMPARISON-FORMAL-001` and `QRH-STRIP-001`.
Total constants are existential; the historical effective-constant claim is separate.

## Checked statement

For T>=3 use the actual zero-occurrence sum Phi, with every ordered pair,
analytic multiplicity and full endpoint weight in **0 < gamma <= T**. Define

\[
 C_T=\frac{T\log T}{2\pi},\qquad
 \mathcal F_T(\alpha)=\frac{2\pi\operatorname{Re}\Phi(T^\alpha,T)}{T\log T}.
\]

`pairNormalizedCorrelation_complex` proves that this real definition, cast to
complex numbers, equals Phi(T^alpha,T)/C_T exactly. Thus taking the real part
has not weakened the statement. In particular this is the manuscript's C_T,
not N(T), T L_T, or a statistic formed by setting beta=1/2.

There exist **absolute positive C1,C2, chosen before T and alpha**, such that

\[
 \left|\mathcal F_T(\alpha)-T^{-2|\alpha|}\log T-|\alpha|\right|
 \le C_1T^{-2|\alpha|}+\frac{C_2}{\sqrt{\log T}}
 \qquad(T\ge3,\ |\alpha|\le1).
\]

This is `pairNormalized_asymptotic`. The function is nonnegative and even for
every real alpha, and its complex-sum representation is real. Endpoints T=3,
alpha=0,+1,-1 are included. Separate checked consequences are

\[
 |\mathcal F_T(0)-\log T|\le C_0,\qquad
 |\mathcal F_T(\pm1)-1|\le\frac{C_e}{\sqrt{\log T}}.
\]

There is no uniform vanishing total error at the origin asserted here. The
T^(-2|alpha|) error remains essential at alpha=0. Quantification is simultaneous,
so the same bounds apply to any choice alpha=alpha(T) in the closed interval.

## Exact error budget and proof dependencies

There are three actual normalized error functions, and four separately retained
bound scales. Write q=log T, and use 1<=X<=T, T>=3.

| Error | Definition | Uniform bound |
| --- | --- | --- |
| Peak | `pairRHSSmallError X T / (T*q)` | A/X² |
| Mean square | `pairRHSLargeError X T / (T*q)` | B/sqrt(q) |
| Comparison | `(2*pi*Re Phi - pairZeroMeanSquare X T)/(T*q)` | D/q + E*X/(T*q) |

`pairNormalized_decomposition` adds these three signed quantities exactly to
q/X²+log X/q. It uses the exact RHS identity and equality of the two mean squares.
`pairNormalized_errors` uses `pairRHSMean_uniform` and
`pairZeroComparison_uniform`, retaining the constants before all parameters.
No artificial splitting of the single comparison error into two signed errors
is required. Since X/(Tq)<=1/q<=1/sqrt(q), the final constants may be A and B+D+E.

For 0<=alpha<=1, `pairNormalized_power` checks 1<=T^alpha<=T,
log(T^alpha)/log T=alpha and (T^alpha)^(-2)=T^(-2 alpha). Negative frequencies
use exact finite-sum inversion Phi(X^(-1),T)=Phi(X,T), proved by exchanging the
two indices and using the even rational denominator. No prime-side bound is
applied to X<1. Nonnegativity uses the previously checked finite norm identity.

For endpoint absorption, log T<=T and sqrt(log T)<=T give
T^(-2)log T<=1/sqrt(log T), and T^(-2)<=1/sqrt(log T). At alpha=0,
1/sqrt(log T)<=1 gives the distinct constant error bound.

All operations are algebraic at fixed parameters and finite pair reindexing.
No new sum/integral interchange or limit is introduced. Distinct complex zeros
with the same ordinate and repeated occurrences remain separate summands.

## Verification

The definition-only interface is `PairAsymptoticDefinitions`; proofs are in
`PairNormalizedSymmetry`, `PairNormalizedAssembly`, and `PairAsymptotic`.
All **16 public theorems** have independent Comparator statements, inventory
entries and axiom reports. The unfinished headline theorem must be rejected for
`sorryAx`. Permitted axioms are only `propext`, `Quot.sound`, and
`Classical.choice`; the external kernel is disabled.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --pair-asymptotic-only
```

The focused run includes this Comparator suite, the negative control, integrated
project build, complete axiom report, analytic coverage and pair/triple/harness
regressions. Earlier Comparator suites are not rerun. The full runner also
includes the new suite. The ledger links successful content-addressed evidence.

## Remaining boundary

The mathematical normalized inequality is now checked with existential constants.
The coverage map records complete finite positivity/symmetry and leaves the
historical `PAIR-ASYMPTOTIC-001` partial because of effectivity and its classical
KV dependency route. Historical ledger statuses and RH-audit scopes are preserved.
The written theorem's effective constants, earlier explicit norm-tail constant,
further test-function and triple analytic statements, and the signed complex-
argument triple o(1) error remain separate obligations. This theorem supplies
no new ordinate-only triple statistic or critical-line proportion.
