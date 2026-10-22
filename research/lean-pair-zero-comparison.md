# Optimized cutoff and uniform pair comparison

Assumptions: `UNCONDITIONAL`. Ledger: `PAIR-ZERO-COMPARISON-FORMAL-001`.
The strip specialization uses the pinned OpenAI **PREPRINT** input through
`QRH-STRIP-001` / `QRH-IMPORT-001`; this is an alternative to the historical
Korobov–Vinogradov proof of `PAIR-COMPARE-001`.

## Statement and conventions

Write L = `pairZeroMeanSquare`, Phi = `pairCorrelationSum` and
Z*(T) = T log² T. There exist absolute positive Ct,Cx, chosen before X,T, such that

\[
 |L(X,T)-2\pi\operatorname{Re}\Phi(X,T)|\le C_tT+C_xX
 \qquad(T\ge3,\quad1\le X\le T).
\]

This is `pairZeroComparison_uniform`. The previously checked identity
`pairCorrelationSum_im` gives Im Phi = 0. The window is **0 < gamma <= T**;
all ordered pairs of actual zero occurrences, including diagonal pairs and
analytic multiplicities, are retained. Distinct complex zeros at a common
ordinate remain separate. X=1, X=T, T=3 and the case split T=5 are included.
No limit or new sum/integral interchange is used in this milestone.

## Proof and dependency table

| Component | Conclusion | Input / range |
| --- | --- | --- |
| Cutoff admissibility | Z* >= 2T; 0 <= log Z* <= 3 log T | T >= 5; elementary logarithms |
| Named optimized errors | truncation <= Ctr X; height <= Ch X^(2B(Z*)) log³ T; extension <= Ce X^(2B(Z*)) log² T and extension <= 0 | Existing uniform errors; no quantitative strip input |
| Small heights | absolute comparison error <= Cs X | 3 <= T <= 5; apply existing errors at Z=10 with B(10)<=1/2 |
| Generic comparison | error <= Cb X^(2B(Z*)) log³ T + Cx X | All X>=1, T>=3; triangle inequality and log T>=1 |
| Fixed strip | B(Z)<=3/8 for every real Z | Finite maximum including zero; `QRH-STRIP-001` |
| Absorption | log³ T <= 384 T^(1/4) | T>=1; exp(y/4)>=(y/4)^3/3!, y=log T |
| Uniform comparison | error <= Ct T + Cx X | 1<=X<=T, T>=3 |

The cutoff cancellation gives an optimized truncation constant 9 times the
previous simple-bound constant. For small heights, one may use
Ctr log²(10) + 125 Ch + 25 Ce. The same optimized estimates retain **three
separate errors**, with truncation O(X), height O(T), and extension O(T) and
nonpositive, for T>=5. No inadmissible optimized cutoff estimate is used below 5.

The generic argument lives in `PairZeroCutoff`; it uses the ordinary critical
strip for its finite-envelope estimates. `PairZeroComparison` explicitly invokes
the imported seven-eighths strip. Its mathematical dependency is recorded even
though other analytic prerequisites already have imported proof dependencies.

The factor 384 is explicit. Total constants remain existential because their
counting/kernel inputs are existential; numerical effectivity is not claimed.
The historical KV envelope, low-height certificate route, and effective-constant
assertion remain incompletely formalized. Their ledger statuses are not promoted.

## Verification

All **12 public declarations** are covered by an inventory, definition-only
Comparator challenges, and the complete project axiom report. The challenge
modules import definitions, not the new proof modules. The unfinished uniform
comparison must fail for `sorryAx`. Only `propext`, `Quot.sound`, and
`Classical.choice` are permitted; the external kernel is disabled.

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --pair-zero-comparison-only
```

This focused run verifies the new suite, combined project build, all axiom
reports, analytic coverage, and pair/triple/harness regressions. It reuses the
prepared pinned dependencies and does not rerun earlier Comparator suites.
The full runner also includes this suite. Successful content-addressed evidence
is linked from the ledger; historical pair/triple RH audits retain their scope.

## Next boundary

The [normalized pair asymptotic](lean-pair-asymptotic.md) now combines this
comparison with the RHS mean square, including all frequency endpoints and
finite symmetry. Effective constants and the historical KV route remain
separate. This does not prove the signed complex-argument error for the
ordinate-only triple statistic.
