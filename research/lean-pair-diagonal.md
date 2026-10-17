# Prime diagonal asymptotic

Assumptions: `UNCONDITIONAL`. Task: proof and formal verification.
Ledger entry: `PAIR-PRIME-DIAGONAL-FORMAL-001`.

## Statement and conventions

For the existing coefficient API (index k denotes n=k+1), set

    a_X(n) = Lambda(n)/sqrt(n) min(n/X,X/n),
    D(X) = sum_n a_X(n)^2,
    D_pp(X) = sum_{n a proper prime power} a_X(n)^2.

There exists one constant C>0, independent of all real X>=1, such that

    |D(X)-log X| <= C,       D(X) <= C log(2X),
    0 <= D_pp(X) <= C log(2X)^3/sqrt(X),       D_pp(X) <= C.

The square-root denominator is also translated exactly to X^(-1/2).
All series are absolutely summable. The exact split is

    D(X) = X^(-2) sum_{n<=X} n Lambda(n)^2
           + X^2 sum_{n>X} Lambda(n)^2/n^3.

The head is inclusive; the tail is strict. A prime or proper prime power
at n=X occurs once. At the knot both weights equal 1/X, and X=1 is included.
The n=0 term in the natural-number API is exactly zero.

**Constants are existential.** No effective PNT threshold or certified numerical
constant is supplied. The historical `PAIR-PRIME-DIAGONAL-001` has an additional
effectivity assertion and therefore retains partial formalization coverage.

## Proof and dependency chain

| Modules | Role |
| --- | --- |
| `PairDiagonalDefinitions`, `PairDiagonalAlgebra` | Existing coefficients, exact weights, absolute convergence and inclusive/strict split |
| `PairDiagonalPNT` | Global bound `abs(psi(u)-u) log(u) <= C u`, from pinned unconditional StrongPNT plus a compact-range Chebyshev bound |
| `PairDiagonalCumulative` | Abel summation of Lambda(n) log(n), subtraction of proper powers, `A(u)=sum_{n<=u} Lambda(n)^2 = u log(u)+O(u)` |
| `PairDiagonalIntegrals`, `PairDiagonalAbel`, `PairDiagonalFinite` | Exact primitives, finite Abel identities and uniform remainder |
| `PairDiagonalAsymptotic` | Fixed-X passage from finite sums to the actual diagonal; uniform final bound |
| `PairDiagonalPowerCount`, `PairDiagonalPowerBall`, `PairDiagonalPowerBound` | Square-root proper-power count, finite dyadic cover, absolute double summation |
| `PairDiagonalEndpoints` | One uniform constant, X=1, integer cutoffs and rpow translation |

For Y>=X>=1 the finite Abel identity is

    S(X,Y) = X^2 A(Y)/Y^3 - X^(-2) integral_1^X A(u) du
             + 3 X^2 integral_X^Y A(u)/u^4 du.

The A(X) boundary terms cancel. Replacing A(u) by u log(u) gives exactly

    log X + 1 - 1/(4X^2) - X^2(2 log Y+3)/(4Y^2).

If `abs(A(u)-u log(u)) <= K u`, the remaining error is at most 3K,
uniformly for Y>=X>=1. Absolute summability and the vanishing upper-endpoint
term justify Y=N tending to infinity at **fixed X**. The resulting constant
is independent of X; no exchange of X and N limits is needed.

The proper-power proof uses the inclusive count

    A_pp(u) <= (4/log 2) sqrt(u) log(2u)^3.

For R_j=2^j X, the nonnegative covering row is supported on proper powers
n<=R_j and has coefficient `8 X^2/R_j^3 * Lambda(n)^2`. Every term is covered
by at least one row. Its total is bounded by

    (32/log 2) [log(2X)^3/sqrt(X)] (j+1)^3 4^(-j).

This summable majorant establishes absolute double summability before the
orders of summation are exchanged. Finally `log(2X)^3/sqrt(X) <= 432`.
All arithmetic and integrals are exact Lean deductions; no numerical
experiment supplies an analytic premise.

## Pinned PNT compatibility repair

The pinned OAI compatibility port removed the global `SmoothExistence`
proof still referenced by `MediumPNT`. A proved namespaced copy already
exists at the same pin as `Erdos970.SmoothExistence`.
`scripts/prepare_lean_diagonal.py` redirects that import and reference,
rejecting unexpected source contents. The reproduction harness runs this
idempotent repair after upstream patch hooks and archives the resulting
dependency diff. Neither dependency pins nor mathematical assumptions change.
The imported StrongPNT and smoothing theorem are included in the axiom audit.

## Verification

The inventory lists 54 public declarations in 12 modules. Seventeen selected
statements have separate definition-only Comparator specifications. Four
central imported inputs have explicit axiom reports: StrongPNT, the proved
smoothing function, finite Abel summation, and the Chebyshev bound.
Only `propext`, `Quot.sound`, and `Classical.choice` are permitted.
An isolated unfinished asymptotic must be rejected for `sorryAx`.

Run `python3 scripts/reproduce_lean.py --skip-bootstrap` to prepare the pinned
PNT source, build, compare, audit, run regressions and archive the result.
The full run passed on 2026-10-17. The content-addressed
[verification manifest](../artifacts/certificates/lean/c14b9eb20247cb235e6fe221b99b35e6387fc146214c427a80bca85005926ece/manifest.json)
records 58 successful commands (including expected rejections), all 17 new
statement comparisons, 810 total axiom reports, 15 unfinished-proof rejection
controls, 26 coverage checks, 70 pair regressions and 126 triple regressions.
All recorded source, output, tool-binary and dependency-diff hashes were
verified against the archive. The run used the existing build cache
(`fresh_project_build=false`) and Lean's default kernel. It does not claim
fresh-checkout or independent external-kernel verification.

## Remaining work

The [optimized prime mean square](lean-pair-prime-mean.md) now combines the
three checked inputs. Next formalize the full prime-side squared norm with
the archimedean main term and explicit-formula remainders. Effective diagonal
and mean-square constants remain separate. The pair and triple correlation
theorems are not promoted by these milestones.
