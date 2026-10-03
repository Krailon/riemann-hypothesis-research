# Work Package B: ordinate-only extension

Task: proof, source review and finite algebra verification. Assumptions:
`UNCONDITIONAL`; `SUPPORT(h<=1-kappa, 0<kappa<1)` for Fourier-test statements.
The finite sensitivity fixture is `SYNTHETIC_MODEL`.

The archived weighted baseline remains complete in its recorded scope.
**The expanded Work Package B target is active and unresolved.** The new
[proof draft](../proofs/triple_ordinate_reduction.tex) makes progress on
kernel removal but does not claim a conventional ordinate-only asymptotic.

## Exact observable and reduction

Write `q=log T`, `b=log(T/(2pi))`, `ell=b/(2pi)`, and `c=16/(3Tq)`.
Use all ordered zero occurrences with multiplicity, including both signs,
all partial diagonals and repeated indices. Only the anchor has the smooth
weight `omega(gamma1/T)`, with omega nonnegative, supported in (1,2), mass one.
For `u=ell(gamma2-gamma1)`, `v=ell(gamma3-gamma1)`, define

`O_T=(T ell)^(-1) sum omega F(u,v)`.

The exact full-zero arguments are
`z=(u-i ell(delta2+delta1), v-i ell(delta3+delta1))`.
Let `Jdelta` be the existing full kernel, `J0` its parameter specialization
at zero horizontal displacement, and `J*=3pi/8`. Then

`R_T^J = (b/q) O_T + E_arguments + E_horizontal + E_gaps`.

All sums are absolutely convergent at fixed T. No global replacement of
actual zero locations by critical-line zeros is made.

## Named error budget

Let `A20(F)=sup (1+max(|u|,|v|))^20 |F(u,v)|` and `W=||omega||infinity`.
All estimates below are for sufficiently large T, with constants independent
of the displayed test seminorms. The proof fixes test, support margin and
smoothing before the height limit.

| Term | Exact definition or source | Current bound/status |
| --- | --- | --- |
| Weighted baseline error | `R_T^J-S3[F]` | Existing named signed-test and localization bounds; o(1) for fixed data. |
| `E_gaps` | `c sum omega (J0-J*) F(u,v)` | `O(W A20/q)`, proved-draft. |
| `E_horizontal` | `c sum omega (Jdelta-J0) F(u,v)` | `O(W A20 (log q)^2/q)`, proved-draft; reflection precedes absolute values. |
| `E_arguments` | `c sum omega Jdelta (F(z)-F(u,v))` | `O(P22(phi) M_T(1-kappa))`; vanishing **open**. |
| Scale error | `(q/b-1) S3[F]` | Exact; O(1/q) for fixed F. |

Exactly,

`O_T-S3 = (q/b)(R_T^J-S3-E_arguments-E_horizontal-E_gaps) + (q/b-1)S3`.

Here `P22(phi)=sum_{|alpha|<=22} ||partial^alpha phi||_1` and the sufficient
nonnegative moment is

`M_T(s)=(Tq)^(-1) sum omega (1+r)^(-20) x^2(1+x)^22 exp(2s x)`,

with `r=max(|u|,|v|)` and `x=q max_j |delta_j|`. It is finite for each T;
no o(1) estimate is proved. Signed cancellation could establish the needed
argument estimate without proving this stronger positive-moment condition.

## Proof route and claim map

| Ledger ID (`ORDINATE-` prefix, `-001` suffix) | Dependencies | Status |
| --- | --- | --- |
| `PAIR-INPUT` | GLSS v4, (6.1) | Proved-draft upper-bound corollary of imported unconditional source. |
| `DENSITY-INPUT` | Simonic, Theorem 1 | Proved-draft corollary of imported explicit density theorem. |
| `TRANSFER` | Existing zero count and kernel profile | Proved-draft exact identity, normalization and convergence. |
| `COUNT` | Pair input plus existing unit counts | Proved-draft bounds on cumulative near/far triple counts. |
| `REAL-KERNEL` | Transfer bounds, counts, density input | Proved-draft removal of the kernel on real test arguments. |
| `ARGUMENT-BOUND` | Transfer and unit counts | Proved-draft quadratic majorant after simultaneous reflection. |
| `ARGUMENT-VANISHING` | Argument bound or a future signed method | **Idea: unresolved estimate.** |
| `TRIPLE` | Weighted theorem, transfer, real-kernel bounds, argument vanishing | **Idea: unresolved ordinate-only theorem.** |

The near count is `H_T(R)<<Tq^2 R^2` for `1<=R<=q^(1/4)`; the global count
is `H_T(R)<<Tq^3(1+R)^4`. A Schwartz tail with exponent 20 is enough.
For horizontal kernel removal, use simultaneous reflection, a second-order
Taylor bound, and the cutoff `D=64 log q/q`. Three dyadic density windows
cover `[T-1,2T+1]`; strict `|delta|>D` agrees with strict `beta>sigma` in the
source. This avoids inferring a triple bound merely from a density-one claim.

## Source review and limits of coverage

See the [primary-source note](literature-notes/ordinate-reduction-inputs.md).
The new imports have not received a full reconstruction of their upstream
proofs. Published numerical inputs underlying the explicit density estimate
are inherited, not replayed; the ledger flags this provenance. No new
computer-assisted theorem or effective close-pair constant is asserted.

The historical pair and triple audits retain their original scope. Their
whole-ledger hashes are refreshed only after checking that the old ledger
is an unchanged byte prefix and that every pre-existing indexed claim block
is identical. The pair record's added provenance metadata then requires a
corresponding triple audit input hash refresh. Neither refresh extends the
old reviews to these new claims. The archived baseline files are untouched.

## Reproduce this extension

```bash
python3 -B -m unittest discover -s scripts -p 'check_triple_ordinate_reduction.py' -v
mkdir -p /tmp/ordinate-reduction-build
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory=/tmp/ordinate-reduction-build proofs/triple_ordinate_reduction.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory=/tmp/ordinate-reduction-build proofs/triple_ordinate_reduction.tex
```

The eight exact regression checks cover telescoping signs, normalization,
reflection with multiplicities and index partitions, colliding centers,
closed horizontal parameter endpoints, support-sector identities, finite
count majorization and microscopic sensitivity. They do not verify analytic
asymptotics. Polynomial and mode fixtures are used for finite identities
only, and are not passed off as admissible Schwartz tests. The full triple
test discovery also includes these checks; the existing PDF harness still
builds the weighted baseline manuscript.

Validation on 2026-10-03 (Python 3.12.3): all 70 pair tests and 117 triple
tests passed. The separate six-page reduction PDF compiled with no remaining
warnings or unresolved references. Both historical audit validators passed;
the old claim blocks and archived baseline remained unchanged. This was a
development-worktree validation, not a newly archived clean-checkout baseline.

## Remaining research step

Prove `E_arguments=o(1)` for the fixed admissible class, or find an alternative
ordinate-only argument. Density at unscaled horizontal distances is
insufficient for the present continuity argument; see
[the recorded failed inference](dead-ends.md#ordinate-transfer-at-microscopic-horizontal-distance).
There is no proof here that the target is impossible or equivalent to RH.
