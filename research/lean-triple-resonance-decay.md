# Decaying prime-power resonance

Task: formal verification. Assumptions: `UNCONDITIONAL`.

For the existing ordered resonance mass, `triplePrimeResonantMass_decay` proves
for every X,Y>=1, with Z=XY,

\[
0\le R_{\rm res}(X,Y)\le C_{\rm res}\frac{\log(2Z)^3}{\sqrt Z},
\quad
C_{\rm res}=8\left(1+\frac6{\log2}\right)
\sum_{j\ge0}(j+1)^3\,4^{-j}.
\]

The positive constant is explicit, with a checked convergent geometric series;
no PNT constant or zero-location hypothesis is used. The scalar envelope tends
to zero. The public uniform-vanishing theorem states that for each eta>0 there
is R>=1 such that the resonance is less than eta whenever X,Y>=1 and XY>=R.
Either individual scale may remain one.

The proof reuses the exact checked grouping by product, preserving all ordered
factorizations and repetitions. The grouped term c(X,Y;n)a_Z(n) vanishes
outside proper prime powers. The existing convolution bound and Lambda(n)<=log n
give the nonnegative majorant

\[
1_{\{n\text{ proper prime power}\}}\,
\frac{v_Z(n)^2\log^3 n}{n},\qquad
v_Z(n)=\min(n/Z,Z/n).
\]

The sharper inclusive count separates squares from exponents k>=3. Overcounting
all integer bases gives, for u>=1,

\[
N_{\rm pp}(u)\le\sqrt u+u^{1/3}\frac{\log u}{\log2}
\le\left(1+\frac6{\log2}\right)\sqrt u.
\]

The last step uses log u<=6u^(1/6). This removes the extra logarithm in the
previous proper-power counting bound without strengthening any assumption.
The count at u=1 is zero.

At R=2^j Z, use the finite ball majorant

\[
B_{Z,R}(n)=1_{\{n\le R,\ n\text{ proper prime power}\}}
\frac{8Z^2}{R^3}\log^3(2R).
\]

Its sum is the displayed scalar coefficient times the proper-power count.
Every original term is bounded by at least one ball. The balls overlap and
are used only as nonnegative majorants. Their sums are bounded by
8 C_pp [log^3(2Z)/sqrt Z] (j+1)^3 4^(-j). The double series is proved absolutely
summable before exchanging the integer and dyadic sums. Parameters are fixed
through these sums; the resulting constant is uniform in both scales.

Endpoints include X=1, Y=1 and X=Y=1. Integer ball cutoffs include equality,
including prime squares. A separate checked inequality retains the p*p
summand explicitly, so equal exponents are not discarded. The existing
ordered convolution identity handles all other ordered factorizations.

Verification compares all 32 public statements against a definition-only
challenge and separately rejects three unfinished proofs: the sharp count,
double summability, and final decay estimate. The focused reproduction also
runs the combined build, complete axiom report and regressions:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-resonance-decay-only
```

Allowed axioms are `propext`, `Quot.sound` and `Classical.choice`; the external
kernel is disabled. The runner archives actual outcomes in a content-addressed
manifest. Python checks validate bookkeeping, not the analytic proof.

This completes the resonance component of `TRIPLE-RETAINED-001`. The mixed
diagonal and sharp first smoothing moment were checked in earlier milestones.
The full retained-term evaluation and its combined error estimates remain to
be assembled. Historical ledger statuses and RH-audit scopes are unchanged;
the signed complex-argument error remains open.
