# Interior weighted test-function passage

Task: formal verification. Assumptions: `UNCONDITIONAL` and
`SUPPORT(compact subset of xi>0, eta>0, xi+eta<1)`.

`tripleTest_theorem` assembles the exact identity, absolute convergence,
quantitative estimate and fixed-test limit for the native weighted full-zero
statistic. For a smooth compactly supported complex test phi in the interior
triangle, the existing project transform is

\[
F(z_1,z_2)=\int_{\mathbb R^2}\phi(\xi,\eta)
 e^{2\pi i(z_1\xi+z_2\eta)}\,d\xi\,d\eta.
\]

`complexFourier_entire` proves joint complex differentiability on C^2.
It differentiates under the integral using a derivative bound on a compact
complex neighborhood times the compact frequency support, dominated by a
constant times |phi|. `complexFourier_schwartz_inversion` supplies a Schwartz
map on the existing Euclidean `FourierPlane`, identifies it with the real
restriction of F, and proves its Fourier transform is phi in project
coordinates. The existing volume-preserving `planeCoords` conversion fixes
the measure convention.

Put B=T/(2pi), L_T=log B/(2pi), and L=log(2T+2). For T>2pi,

\[
\mathcal R^K_{3,T}
 =8\sum_{i_1,i_2,i_3}K_T(i_2,i_3,i_1)F(z_{21},z_{31})
 =\int_{\mathbb R^2}\phi(\xi,\eta)
 C_{3,T}(B^\xi,B^\eta)\,d\xi\,d\eta,
\]

where z_j1=L_T((gamma_j-gamma_1)-i(delta_j+delta_1)). The checked phase
identity preserves both negative imaginary shifts and the sums of horizontal
displacements. `tripleTestToMaster` is an explicit equivalence taking anchor
order (i1,i2,i3) to master order (i2,i3,i1), so the third kernel slot is
conjugated. Every ordered zero occurrence, both ordinate signs, multiplicity
indices and every partial diagonal remain present. The factor eight is
unchanged; 1/T is already inside K_T. No extra L_T^2 or Jacobian is inserted.

The frequency/zero interchange is preceded by a summable majorant. At unit
prime scales the master estimate proves

\[
8\sum_v\|K_T(v)\|\le A L^3.
\]

The open critical strip, without RH, gives |coefficient(X,Y;v)|<=XY for
X,Y>=1. On support in the closed interior triangle
Omega_epsilon={xi,eta>=epsilon, xi+eta<=1-epsilon}, this yields

\[
\sum_v\int\|\phi(p)\,8\,\operatorname{coefficient}(B^{p_1},B^{p_2};v)
 K_T(v)\|\,dp\le A\|\phi\|_1B^{1-\varepsilon}L^3.
\]

The proof establishes summability of these integral norms before exchanging
the series and integral. It also proves absolute convergence of the evaluated
zero sum and integrability of the frequency side. Independent rectangular
occurrence cutoffs converge at fixed T, phi and omega. Real-axis Schwartz
decay is not used as a bound at complex zero arguments.

For 0<epsilon<1/3 the quantitative estimate is

\[
|\mathcal R^K_{3,T}|\le C\|\phi\|_1(1+W+\|\omega'\|_1)
 B^{-\varepsilon}L^4,
\]

where omega satisfies `TripleBudgetWeight` and W>=0 is any pointwise upper
bound for omega. One absolute C is chosen before the test, smoothing,
margin and height. The proof substitutes R=B^epsilon directly into the
checked lower-scale retained and additive estimates: X,Y>=R and
XY<=B/R<=T/R. This is an equivalent, simpler route than the manuscript's
theta_T and epsilon_T conversion, and uses no varying-margin limit theorem.
The scalar envelope equals a fixed multiple of T^(-epsilon)L^4 and tends
to zero. Compact support supplies W, so the fixed-weight limit needs no
additional boundedness premise.

Every compact subset of the open triangle admits a positive margin strictly
below 1/3; the empty set is handled separately. Thus the final limit applies
to every smooth compactly supported test in that open triangle. A checked
nonzero test equals one at (1/4,1/4) and has support in [3/16,5/16]^2 inside
Omega_(1/8). Other checks include the zero test, coordinate exchange of
frequency integrals and margins, and inclusive inequalities on all interior
margin boundaries. T>2pi remains strict.

The historical numerical-effectiveness assertion is not promoted: constants
remain existential through existing analytic inputs. The mathematical
statement of `TRIPLE-TEST-FUNCTION-001` is covered separately by
`MASTER-TEST-FUNCTION-FORMAL-001`. Frequency axes, the origin, the outer
support boundary and the ordinate-only signed complex-argument error are
not resolved by this theorem.

All 31 public declarations have independent definition-only Comparator
specifications. Four unfinished-proof controls cover joint regularity,
the interchange identity, the quantitative bound and the interior limit.
The focused harness runs these checks, the combined project build, the full
axiom report, analytic coverage and regressions:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-test-function-only
```

The permitted axioms are `propext`, `Quot.sound` and `Classical.choice`.
The external kernel is disabled. Actual results are archived in a
content-addressed certificate; Python checks bookkeeping, not analysis.

Next: formalize the frequency-axis and origin contributions.
