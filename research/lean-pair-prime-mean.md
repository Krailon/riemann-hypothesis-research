# Optimized prime mean square

Task: proof and formal verification. Assumptions: `UNCONDITIONAL`.
Ledger entry: `PAIR-PRIME-MEAN-FORMAL-001`.

## Statement and exact errors

Use the existing actual series P(X,t), coefficients
`Lambda(n)/sqrt(n) min(n/X,X/n)` (API index k denotes n=k+1), and diagonal D(X).
Define

    M(X,T) = integral_0^T |P(X,t)|^2 dt,
    E_offdiag(X,T) = M(X,T) - T D(X),
    E_diagonal(X,T) = T D(X) - T log X,
    L2(X,T) = sqrt(M(X,T)).

There exists C>0, independent of real T>=3 and 1<=X<=T, such that

    |E_offdiag(X,T)| <= C sqrt(T X log(2X)),
    |E_diagonal(X,T)| <= C T,
    L2(X,T) <= C sqrt(T log(2X)).

The decomposition `M = T log X + E_diagonal + E_offdiag` is exact.
A separate corollary bounds `abs(M-T log X)` by
`C (T + sqrt(T X log(2X)))`. This is an absolute error statement, including
X=1; it is not a relative asymptotic at a vanishing main term.
The integrand is interval integrable and M is nonnegative for T>=0,
so the square-root expression is the conventional integral L2 norm.

Proper prime powers remain included. The nearby pairs are ordered and their
logarithmic cutoff is strict. E_offdiag includes the diagonal cost of the
Fourier majorants; it denotes the entire error after subtracting T D.

## Bandwidth and proof

Set ell=log(2X) and delta=(1/2)sqrt(ell/(T X)).
The bandwidth module proves `0<ell<=X`, `X<=T ell`, and consequently

    1/(2T) <= delta <= 1/2,
    ell/delta = 2 sqrt(T X ell),
    T delta X = sqrt(T X ell)/2.

The lower admissibility bound uses X<=3/2 or X>=3/2, together with
log(2)>=1/2 and log(3)>=1. The upper bound uses
log(2X)=log(2)+log(X)<=1+(X-1). All logarithm inequalities come from
checked mathlib proofs, not floating-point evaluation.

If D(X)<=A ell and Q(X,delta)<=B delta X, the existing Fourier mean-value
bound gives the explicit relative-to-input-constants coefficient

    |E_offdiag| <= (1024 A + 1025 B/2) sqrt(T X ell).

The local theorem then discharges both premises with the checked diagonal
and weighted sieve estimates. The diagonal error follows by multiplication
by T. Finally `sqrt(T X ell)<=2 T ell` yields an upper bound for M and its
square root. No new infinite-series exchange is introduced: the existing
prime-series specialization already justifies its fixed-X,T limits.
The final bounds are uniform throughout the stated closed parameter range.

| Module | Role |
| --- | --- |
| `PairPrimeMeanDefinitions` | Definition-only bandwidth, integral, named errors and norm |
| `PairPrimeMeanBandwidth` | Admissibility and exact balancing identities |
| `PairPrimeMeanEstimate` | Integrability, decomposition, arithmetic substitution, individual errors and norm |
| `PairPrimeMean` | Combined error, common constant and X=1, X=T, T=3 endpoints |

Constants are **existential**, inherited from the diagonal milestone. The
historical `PAIR-PRIME-MEAN-001` also asserts effectivity; its coverage remains
partial solely for that assertion. This milestone neither promotes the full
RHS mean square nor the pair/triple correlation theorems.

## Verification

All 18 public declarations in four modules have separate definition-only
Comparator specifications and axiom reports. Three imported logarithm bounds
are also audited. Only `propext`, `Quot.sound`, and `Classical.choice` are
permitted; an isolated unfinished uniform theorem must be rejected.
Coverage checks preserve the effectivity gap and the outstanding RHS theorem.

Run `python3 scripts/reproduce_lean.py --skip-bootstrap` for the complete
build, Comparator, axiom, rejection-control and regression suite.
The full run passed on 2026-10-17. The content-addressed
[verification manifest](../artifacts/certificates/lean/7bd9063b975aef107776d962d935306e46da3d06e3e53d937d2ce8b5720b3a46/manifest.json)
records 61 successful commands (including expected rejections), all 18 new
statement comparisons, 831 total axiom reports, 16 unfinished-proof rejection
controls, 28 coverage checks, 70 pair regressions and 126 triple regressions.
All recorded source, output, tool-binary and dependency-diff hashes were verified.
This run used the existing build cache (`fresh_project_build=false`) and Lean's
default kernel; it does not claim a fresh-checkout or independent external-kernel
verification.

## Next step

Formalize the full prime-side squared norm, combining this prime mean square
with the archimedean main term and the named explicit-formula remainders.
Numerical effectivity of the diagonal and mean-square constants remains
separate work.
