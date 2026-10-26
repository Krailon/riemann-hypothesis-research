# Full retained-term evaluation

Task: formal verification. Assumptions: `UNCONDITIONAL`.

`tripleRetained_evaluation` assembles the checked mixed diagonal, first
smoothing moment, and resonance decay for every admissible `TripleBudgetWeight`,
T>=3 and X,Y>=1. With q=log T, Z=XY, L=log(2T+2), it proves exactly

\[
M_T=\frac{q^3}{Z^2}+(q+\mu_\omega)G(X,Y)+E_D+E_J-R_{\rm res}(X,Y),
\]

for the existing complex-valued `tripleBudgetRetained`, with an explicit real
to complex coercion. The definitions are the manuscript's:

\[
\begin{aligned}
G(X,Y)&=\frac{(1+\log Y)\log(XZ)}{2Y^2}
       +\frac{(1+\log X)\log(YZ)}{2X^2},\\
\Delta(a,b)&=D(a,b)-\operatorname{Main}(\min(a,b),\max(a,b)),\\
E_D&=J_1\{\Delta(X,Z)/Y+\Delta(Y,Z)/X\},\\
E_J&=(J_1-q-\mu_\omega)G(X,Y).
\end{aligned}
\]

Put B(X,Y)=(1+log Y)/Y^2+(1+log X)/X^2. One absolute C>0 is chosen before
the smoothing weight, height, and either prime scale. Uniformly,

\[
|E_D|\le CLB(X,Y),\qquad 0\le E_J\le2G(X,Y)/T,
\quad G(X,Y)\ge0,\quad 0\le\mu_\omega\le\log2.
\]

The exact negative resonance term remains present. Using the previously
checked explicit resonance constant C_res and scale S(Z)=log(2Z)^3/sqrt Z,
the combined additive estimate is

\[
\left|M_T-\left(q^3/Z^2+(q+\mu_\omega)G\right)\right|
\le CLB+2G/T+C_{\rm res}S(Z).
\]

The diagonal constant remains existential through the checked PNT input.
The smoothing constant two and the convergent-series resonance constant stay
explicit. No relative asymptotic or numerical effectiveness of C is claimed.
The historical effectiveness assertion is the only remaining qualification
for formal coverage of `TRIPLE-RETAINED-001`.

The algebra orders the diagonal arguments using X<=XY and Y<=XY, then
checks the leading-term normalization exactly. The error bounds use the
existing J1 bound and the uniform mixed-diagonal estimate. No new limiting
argument is needed. Exchange symmetry of the resonance uses its already
absolutely summable ordered product series; all other symmetry checks are
algebraic. All prime powers and multiplicities retain their prior conventions.

Checked specializations include equal scales, either unit scale, X=Y=1,
and the closed endpoint T=3. At X=Y=1, G=0, B=2 and E_J=0, and the exact
identity retains 2 J1 D(1,1)-R_res(1,1) beside q^3. The whole retained
expression and each named correction are symmetric under exchanging X,Y.

Verification compares all 28 public declarations against a definition-only
challenge, with three unfinished-proof controls for the exact identity,
uniform diagonal error, and consolidated theorem. The focused mode runs the
combined build, full axiom report and regressions:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-retained-only
```

Allowed axioms are `propext`, `Quot.sound` and `Classical.choice`; the external
kernel is disabled. Actual results are archived in a content-addressed
manifest. Python checks verify bookkeeping and harness behavior.

The interior-vanishing corollary remains a separate milestone. Historical
ledger statuses and RH-audit scopes are preserved; the signed complex-argument
error for an ordinate-only statistic remains open.
