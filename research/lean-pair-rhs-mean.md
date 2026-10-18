# Full explicit-formula mean square

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
Ledger entry: `PAIR-RHS-MEAN-FORMAL-001`.

## Statement

Use the actual prime series P(X,t) and all four actual PAIR-EF-001 remainders.
For t>=0 put A(X,t)=log(t+2)/X, H=E_arch+E_DS+E_pole+E_trivial,
r=-P+A+H, and R(X,T)=integral_0^T |r(X,t)|^2 dt.
The checked explicit formula identifies r with the existing full zero series,
so R equals its squared integral with exactly the same normalization.
Both integrands are interval integrable.

There exist absolute constants C1,C2>0, independent of real T>=3 and
1<=X<=T, for which

    R = T log(T)^2/X^2 + T log X + E_small + E_large,
    |E_small| <= C1 T log(T)/X^2,
    |E_large| <= C2 T sqrt(log T).

The decomposition is exact. A further corollary bounds the absolute difference
between the actual zero-side squared integral and the two main terms.
All endpoints X=1, X=T and T=3 are included; the integrands include t=0.
Proper prime powers and all zero occurrences with their original horizontal
coordinates and multiplicities remain in the series.

The constants are **existential**, inherited from the optimized prime mean
square. This recovers the estimates of historical `PAIR-RHS-MEAN-001`,
including its sharp mixed term, but leaves its numerical effectivity assertion
unformalized. No normalized pair or triple asymptotic is promoted.

## Exact errors and estimates

Write q=log T and ell=log(2X). For j in {arch, DS, pole, trivial}, define

    E_P,j = -2 Re integral_0^T P conjugate(E_j),
    E_A,j =  2 Re integral_0^T A conjugate(E_j),
    E_PA  = -2 Re integral_0^T P conjugate(A),
    E_H2  = integral_0^T |H|^2,
    E_A2  = integral_0^T |A|^2 - T q^2/X^2.

The prime diagonal and off-diagonal errors are exactly those of the preceding
[prime mean-square milestone](lean-pair-prime-mean.md).

| Named term | Checked control | Final group |
| --- | --- | --- |
| E_A2 | <=64 T q/X^2 in absolute value | E_small |
| E_A,arch, E_A,DS | O(T q/X^2), individually | E_small |
| E_diagonal | O(T) | E_large |
| E_offdiag | O(sqrt(T X ell)) | E_large |
| E_PA | <=20 log(T+2)/sqrt X in absolute value | E_large |
| Each E_P,j | Cauchy–Schwarz with that remainder's own L2 norm | E_large |
| E_A,pole, E_A,trivial | O(T sqrt(q)), individually | E_large |
| E_H2 | <=4 sum_j integral_0^T |E_j|^2; O(T) on this range | E_large |

Thus E_small=E_A2+E_A,arch+E_A,DS and
E_large=E_diagonal+E_offdiag+E_PA+sum_j E_P,j+E_A,pole+E_A,trivial+E_H2.
Signs are checked before taking any absolute values.
With C from `pairPrimeMean_uniform` and K=|C_arch|+C_DS+32, the proof takes

    C1 = 64 + 8 K,
    C2 = 3 C + 40 + 16 C K + 8 K + 16 K^2.

Thus the final existential dependence is inherited from the prime mean-square
constant; the assembly itself provides explicit constants relative to that input.

The individual L2 bounds are

    ||A||_2 <= 2 sqrt(T) q/X,
    ||E_arch||_2 <= |C_arch| sqrt(T)/X,
    ||E_DS||_2 <= C_DS sqrt(T)/X,
    ||E_pole||_2 <= 8 sqrt(X),
    ||E_trivial||_2 <= 24 X^(-5/2).

The two decaying remainders use the integrable majorant (1+t^2)^(-1)
and its checked mass pi<4. The norm of H is never substituted for an
individual remainder before the cross terms are classified. The final
square bound uses the finite inequality |sum of four terms|^2 <=4 sum |term|^2.

## Oscillation and interchanges

Integration by parts proves, for omega>0 and T>=0,

    |integral_0^T log(t+2) exp(-i omega t) dt| <= 2 log(T+2)/omega.

The boundary at t=0 and the integral of 1/(t+2) are included explicitly.
The coefficient at n=1 is zero. For the positive integers n>=2,
Lambda(n)/log n<=1 gives

    sum_n a_X(n)/log n <= 5 sqrt X.

The proof splits at floor(X): the finite part is at most sqrt X;
the strict upper tail is bounded by integrating u^(-3/2), using
floor(X)<=X<=2 floor(X). This includes X=1 and every integral prime-power
cutoff. The resulting bound is |E_PA|<=20 log(T+2)/sqrt X.

For each fixed X,T, the sum/integral interchange is justified by the explicit
integral-norm majorant T log(T+2) a_X(n)/X and the checked absolute convergence
of the coefficient series. No cancellation is used to establish this
interchange. All later bounds are uniform on the stated closed range.

## Modules and verification

| Module | Role |
| --- | --- |
| PairRHSDefinitions | Definition-only observables and named errors |
| PairRHSArchIntegrals | Exact logarithmic primitive and archimedean square error |
| PairRHSContinuity | Actual-term continuity, integrability and zero-series identification |
| PairRHSL2 | Compact-interval Cauchy–Schwarz |
| PairRHSRemainderNorms | Individual archimedean and remainder norms |
| PairRHSOscillation | Logarithmic integration by parts |
| PairRHSPrimeWeight | Coefficient/log summability and sqrt(X) bound |
| PairRHSPrimeArch | Absolute interchange and sharp mixed error |
| PairRHSExpansion | Exact signed expansion |
| PairRHSScales | Uniform height comparisons |
| PairRHSCrossTerms | Individual cross terms and four-remainder square |
| PairRHSMean | Two error budgets, zero-side statement and endpoints |

All 55 public declarations have definition-only Comparator specifications and
axiom reports. Four additional imported analytic inputs are audited; existing
reports already cover the imported absolute integral/series interchange. Only `propext`,
`Quot.sound` and `Classical.choice` are permitted. The unfinished uniform
statement must be rejected. The coverage map now explicitly includes the
historical RHS theorem as a root and retains its effectivity gap.

Verification completed on 2026-10-18. The
[successful verification manifest](../artifacts/certificates/lean/438877da8b2056172edeedb183645785111c2ecfffb065ecd27231cd08423c49/manifest.json)
records 65 successful checks: 61 reused command records and four final checks.
It includes all 55 new statement comparisons, 890 total axiom reports,
17 expected unfinished-proof rejections, 31 coverage tests, 70 pair regressions
and 126 triple regressions.

The [initial full run](../artifacts/certificates/lean/eeb48a04626ab4714db4c8a625bceece49f36cf52d9d9fdf53131d651f52945f/manifest.json)
passed every comparison and rejection control, then failed because AxiomReport
omitted the new RHS module import. The narrowly scoped
[recovery script](../scripts/recover_lean_axiom_report.py) verified that all
recorded proof sources, comparison specifications, tool binaries, dependency
pins and actual dependency diffs were identical. It permitted only addition of
that one report import, then reran the complete axiom report, coverage checks
and pair/triple regressions. The initial failure is preserved and each reused
command explicitly names its source manifest. The ordinary reproduction
command below now includes the repaired report.

All recorded source, output, tool, patch and dependency-diff hashes were
verified against the final archive. This verification used the existing build
cache (`fresh_project_build=false`) and Lean's default kernel; it does not
claim a fresh-checkout or independent external-kernel verification.

Run `python3 scripts/reproduce_lean.py --skip-bootstrap` for the complete suite.

## Next step

Assemble the normalized pair-correlation asymptotic from this mean square and
the zero-side comparison. Effective numerical constants remain separate work.
