# Uniform interior vanishing

Task: formal verification. Assumptions: `UNCONDITIONAL`.

For every normalized admissible `TripleBudgetWeight` omega, write
L=log(2T+2). The two quantitative theorems are

\[
\begin{aligned}
\|M_T(X,Y)\|&\le C_M T^{-\varepsilon}L^3,\\
\|C_{3,T}(X,Y)\|&\le C_C(1+W+\|\omega'\|_1)T^{-\varepsilon}L^4,
\end{aligned}
\]

uniformly for 0<epsilon<1/3, T>=3, T^epsilon<=X,Y and
XY<=T^(1-epsilon). Here M is the existing complex-valued
`tripleBudgetRetained`, C is `tripleMasterObservable`, and W>=0 is any
pointwise upper bound for omega. The derivative norm is the existing
`fourierDerivativeL1 omega 1`. The constants are chosen before omega,
W, epsilon, T, X and Y, not separately for each margin.

The proof first uses R>=1, X,Y>=R, XY<=T/R. It derives X,Y,XY<=T and
sqrt(XY)>=R. The separately checked scalar estimates are

\[
 B(X,Y)\le4L/R,\quad 0\le G(X,Y)\le4L^2/R,\quad
 0\le (\log T)^3/(XY)^2\le L^3/R,\quad
 S(XY)\le L^3/R.
\]

Consequently the main expression P is at most 9L^3/R, while
|E_D|<=4K L^3/R, 0<=E_J<=8L^3/R and 0<=R_res<=C_res L^3/R.
The exact signed identity M=P+E_D+E_J-R_res gives
|M|<=(17+4K+C_res)L^3/R. These deliberately relaxed estimates are
sufficient for the corollary; the sharper retained-term estimates remain
available in their original modules. Substitution R=T^epsilon gives the
first theorem. The checked additive error estimate and L>=1 give the second.

For fixed positive epsilon and fixed smoothing, both expressions tend
uniformly to zero on the moving range: for every eta>0, eventually in T,
every admissible X,Y has norm below eta. Compact support supplies a finite W,
so `tripleInterior_fixed_weight_limit` needs no extra weight-bound premise. The retained cubic envelope is
squeezed below the previously checked quartic envelope; the observable uses
that quartic envelope directly. No new sum/integral or limit interchange is
introduced. All infinite series were already defined at fixed parameters.

The endpoint declarations check T=3, the lower corner X=Y=T^epsilon,
and the upper corners (T^epsilon,T^(1-2epsilon)) and its exchange at the
level of admissible ranges. The uniform bounds use inclusive inequalities
throughout; exchanging X and Y preserves both exact observables. Epsilon
stays strictly between zero and one third.

The result retains full zero coordinates, all occurrence multiplicities,
and all partial diagonals from the master observable. It makes no assertion
on the frequency axes, the outer support boundary, or an ordinate-only
statistic. The signed complex-argument error remains open.

The absolute constants remain existential through the checked diagonal and
prime mean-square inputs. The mathematical inequalities and uniform limits
of `TRIPLE-INTERIOR-VANISHING-001` are covered; its historical numerical-
effectiveness assertion is not promoted. The formal claim is recorded
separately as `MASTER-INTERIOR-VANISHING-FORMAL-001` after verification.

All 21 public declarations are compared with a definition-only challenge.
Three unfinished-proof controls cover the retained bound, observable bound,
and observable uniform limit. The focused harness runs the combined build,
complete axiom report, coverage and regressions:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-interior-vanishing-only
```

Only `propext`, `Quot.sound` and `Classical.choice` are permitted; the external
kernel is disabled. Actual results are archived in a content-addressed
certificate. Python verifies bookkeeping and harness behavior, not analysis.

Next: the interior weighted test-function passage, `TRIPLE-TEST-FUNCTION-001`.
