# Approximate functional equation: checked prerequisites and remaining proof

Assumptions: **UNCONDITIONAL**. The requested full AFE formalization is **not
complete**. The uniform chi-phase estimate is proved; the uniform sharp two-sum
remainder is not yet proved. No density estimate is discharged by this work.

## Pinned downstream statement

The source is Simonič, *Explicit zero density estimate for the Riemann zeta-function*,
[arXiv:1910.08274v2](https://arxiv.org/pdf/1910.08274v2), Theorems 4 and 6,
Corollary 1, and Section 3.1. This is the same author version already used in
`literature-notes/ordinate-reduction-inputs.md`; no new journal-version comparison
is claimed. The pinned PNT `ZetaAppendix.proposition_dadaro` is a one-polynomial
approximation, not the asymmetric two-polynomial AFE. It is not imported here.

Write s=sigma+it, q=|t|/(2*pi), and

    P(s,x) = sum_{1<=n<=floor(x)} n^(-s),
    R(s;x,y) = zeta(s)-P(s,x)-chi(s)*P(1-s,y).

Here chi is exactly the existing `pairChi`. The remaining target is one absolute
C>0, independent of sigma,t,x,y, such that for 1/2<=sigma<=1, |t|>=2*pi,
1<=x<=y and xy=q,

    |R(s;x,y)| <= C*x^(-sigma),
    |R(s;y,x)| <= C*q^(1/2-sigma)*x^(sigma-1).

All positive-integer cutoff terms are included with full weight. Both height
signs, integer x or y, sigma=1/2, sigma=1, and |t|=2*pi are retained. The bound
must not gain an uncontrolled logarithm or a constant depending on sigma-1/2.

## Checked mathematics

The exact remainder is defined as a difference, with algebraic identities kept
separate from estimates. The functional equation is proved at every nonreal s;
chi(s)*chi(1-s)=1 follows from Gamma reflection, not cancellation of zeta(s).
Conjugation and R(s;y,x)=chi(s)R(1-s;x,y) therefore also hold at zeta zeros.
The exact chi factor has norm one on the critical line at nonzero heights.

The explicit phase is

    chiTilde(sigma,t) = q^(1/2-sigma)
      * exp(i*(-t*log(q/e)+sign(t)*pi/4)).

Its conjugation, modulus, critical-line modulus and product at opposite heights
are checked. Finite polynomial bounds, inclusive integer jumps, measurability,
and bounded-interval integrability are proved without continuity across floor
jumps. The actual moving scales sqrt(t*mu1/(2*pi*mu2)) and
sqrt(t*mu2/(2*pi*mu1)) satisfy the required product and ordering on t>=T when
1<=mu1<=mu2<=T/(2*pi); all four polynomials in the twisted expansion are integrable.

Complex Stirling is proved from a convergent correction series, not assumed:

    F(z) = (z-1/2)*log(z)-z,
    d(z) = (z+1/2)*log(1+1/z)-1,
    c(z) = sum_{n>=0} d(z+n).

For Re z>=0 and |z|>=2 the series is absolutely convergent, |c(z)|<=8/|z|,
and its tail after N terms is bounded by 8/|z+N|. A quadratic Taylor estimate
bounds d, and a positive telescoping majorant justifies every infinite sum.
Finite Gamma-sequence identities and the real Stirling limit identify exactly

    Gamma(z) = exp(F(z)+log(2*pi)/2+c(z)).

Gamma recurrence proves the closed Re z=0 endpoint. Consequently the relative
error against exp(F(z)+log(2*pi)/2) is at most 16/|z| for |z|>=8.
All logarithms in this argument are principal, with product identities checked
on the relevant argument domains. No imaginary constant is discarded.

The vertical phase error is at most 9/t for 0<=a<=1/2 and t>=2. The exact sine
factorization then proves

    |chi(s)-chiTilde(sigma,t)| <= C*q^(1/2-sigma)/|t|

uniformly on the entire requested strip and height range. The proof gives C=20
for positive t>=18; bounded-height compactness and conjugation supply one
existential absolute constant for all |t|>=2*pi. Its numerical value is not
extracted. `afe_phase_replacement_uniform` bounds the resulting change in the
actual remainder by C*x^(-sigma) and C*q^(1/2-sigma)*x^(sigma-1), respectively,
in the two cutoff orders. This proves only the phase-replacement error, not R.

For any fixed H>=2*pi a separate compactness argument proves
|R(s;x,y)|<=C_H*x^(-sigma) on 0<=sigma<=1 and 2*pi<=|t|<=H, with x,y>=1 and
2*pi*x*y=|t|. The quantifier order is **forall H, exists C_H**. This theorem
cannot be used as the missing high-height bound.

The contour denominator has a uniform explicit bound: if z is at distance at
least 1/4 from every 2*pi*i*n, then |exp(z)-1|>=1/6 and its inverse norm is <=6.
A local logarithm near 1 proves this via an explicit integer winding; no numerical
minimum or unproved minimum principle is used. The fixed parameters
r0=lambda0=c=1/4, d=4 satisfy the source's four admissibility inequalities.

## Fixed-radius Hankel representation

The positive-ray Mellin identity and its inclusive sharp tail now have checked
absolute-convergence proofs. For Re(s)>1 and any integer m>=0,

    integral_0^infinity u^(s-1)*exp(-m*u)/(exp(u)-1) du
      = Gamma(s)*(zeta(s)-P(s,m)).

The series/integral exchange uses the summable exact integrals of the absolute
values of the Laplace terms. The tail starts at m+1, so the m-th term has full
weight in P. The ray truncated below at any r>0 is absolutely integrable for
every complex s; its dependence on s is entire. Its proof uses an explicit
real-power majorant and the checked Mellin differentiation theorem.

Freeze the positive-axis branch and normalization as

    Lplus(z) = log(-z)+pi*i,
    K(s,m,z) = exp((s-1)*Lplus(z))*exp(-m*z)/(exp(z)-1),
    A(s) = exp(-pi*i*s)*Gamma(1-s)/(2*pi*i),
    J(s,m,r) = counterclockwise integral_{|z|=r} K(s,m,z) dz.

For every nonreal s, integer m>=0 and **0<r<=1/2**, Lean proves

    zeta(s)-P(s,m) = A(s) * [J(s,m,r)
      + (exp(2*pi*i*s)-1)
          * integral_r^infinity u^(s-1)*exp(-m*u)/(exp(u)-1) du].

The two rays run toward the circle on the upper bank of the cut and away on
the lower bank. Their difference supplies the displayed jump. The circle is
an actual circle integral, not a formal residue symbol. On 0<r<=1/2,

    |J(s,m,r)| <= 4*pi*r^(Re(s)-1)*exp(2*pi*|Im(s)|+m/2).

Its r->0 limit is taken only for fixed m,s with Re(s)>1. Rectangle Cauchy
integration in the logarithmic variable proves radius independence and the
initial identity. Entire dependence of the fixed circle and ray terms then
extends the identity separately on the connected upper and lower half-planes.
This does not take a shrinking-circle limit when Re(s)<=1.

The coefficient at each nonzero lattice pole is proved using the actual
punctured limit defining the imported simple-pole residue. In particular,

    A(s)*(2*pi*i)*sum_{k=1}^N [Res_{2*pi*i*k} K + Res_{-2*pi*i*k} K]
      = -chi(s)*P(1-s,N).

The sign, factor 2*pi*i, both lattice halves and inclusive upper endpoint are
checked, including N=0. This is the residue sum; crossing these poles on the
saddle contour still needs a deformation theorem. A wrapper substitutes
m=floor(x) in the exact fixed-radius identity without changing integer weights.

## Remaining implementation

1. Deform the checked fixed-radius Hankel contour to the source's saddle
   contour, with finite paths, explicit pole detours and the checked paired
   residues. The source's sharp two-sum identity is not yet a Lean theorem.
2. Bound its four contour pieces, including the saddle segment and any pole
   detour, by an absolute multiple of x^(-sigma) on 0<=sigma<=1 and x<=y.
   First use finite paths and then prove the infinite-tail limits uniformly.
3. Use the checked reflection identity and chi-phase bounds for reversed
   cutoffs, absorb the checked bounded-height range, and assemble the global
   exact and explicit-phase AFE statements and downstream error witnesses.

The weighted second moment, mollifier estimates, boundary-zero extensions,
analytic density theorem, close-pair bounds and signed-error limit remain later
obligations. The existing Littlewood theorem's hypotheses are unchanged.

## Verification

The suite covers 141 public statements in 20 modules with definition-only Comparator contracts,
23 unfinished rejection controls, complete axiom reporting and scope regressions.
Only propext, Quot.sound and Classical.choice are permitted. Python checks record
coverage and hypothesis boundaries; they do not prove analytic estimates.

    python3 scripts/reproduce_lean.py --reuse-dependencies --approximate-functional-only --control-jobs 8

The focused mode also builds the combined project and runs the existing coverage,
harness, control-pool and pair/triple regressions. The default reproduction
includes the new suite. A passing certificate covers the checked prerequisites
including chi-phase transfer and the fixed-radius Hankel identity; it does not certify the unfinished AFE theorem.
