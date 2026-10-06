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
| `E_arguments` | `c sum omega Jdelta (F(z)-F(u,v))` | Exactly `E_even+E_kernel-mix`; vanishing **open**. The earlier `O(P22 M_T)` bound remains valid. |
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
| `SIGN-AVERAGE` | Transfer, kernel profile, unit counts | Proved-draft eight-reflection identity, parity, positivity of the even kernel coefficient and odd-coefficient gap factor. |
| `QUADRATIC` | Sign average and argument bound | Proved-draft full quadratic term including kernel derivatives; controlled remainder for `x<=1`. |
| `CANCELLATION-BUDGET` | Sign average, quadratic term, counts | Proved-draft even and kernel-mixing moment bounds. |
| `DENSITY-MIX` | Cancellation budget, density and counts; baseline and transfer for the concluding equivalence | Proved-draft vanishing kernel mixing on the smaller support `h<=s<331/4000`. |
| `CONSTANT-KERNEL` | Sign average, real-kernel estimates, cancellation budget, density mixing and transfer | Proved-draft constant-kernel replacement with a vanishing error on `h<=s<331/4000`; kernel-free remaining criterion. |
| `ARGUMENT-VANISHING` | Argument bound or a future signed method | **Idea: unresolved estimate.** |
| `TRIPLE` | Weighted theorem, transfer, real-kernel bounds, argument vanishing | **Idea: unresolved ordinate-only theorem.** |

The near count is `H_T(R)<<Tq^2 R^2` for `1<=R<=q^(1/4)`; the global count
is `H_T(R)<<Tq^3(1+R)^4`. A Schwartz tail with exponent 20 is enough.
For horizontal kernel removal, use simultaneous reflection, a second-order
Taylor bound, and the cutoff `D=64 log q/q`. Three dyadic density windows
cover `[T-1,2T+1]`; strict `|delta|>D` agrees with strict `beta>sigma` in the
source. This avoids inferring a triple bound merely from a density-one claim.

## Cancellation after eight independent reflections

Set `a1=b delta1(xi+eta)`, `a2=b delta2 xi`, `a3=b delta3 eta`, with
anchor-first slot order. Define `J_S` as the average of the eight reflected
kernels weighted by `prod_{j in S} epsilon_j`. The exact averaged frequency
factor in `E_arguments` is

`J_empty (prod_j cosh(a_j)-1) + sum_{S nonempty} J_S prod_{j in S}sinh(a_j) prod_{j not in S}cosh(a_j)`.

After pairing with `c omega phi exp(2pi i(u xi+v eta))` and summing, these
give `E_even` and `E_kernel-mix`, respectively. The whole ordered sum is
invariant under independent reflections. Individual index-diagonal classes
need not be invariant. The proof uses symmetric finite ordinate cutoffs and
an integrable kernel majorant before interchanging Fourier integration and
the zero sums.

The coefficients satisfy `conjugate(J_S)=(-1)^|S| J_S` and
`|J_S|<=C prod_{j in S}|delta_j|`. Odd-cardinality coefficients additionally
gain `min(|a|+|d|,1)` and vanish at zero vertical gaps. Although `J_empty>0`,
the Fourier-paired expression remains oscillatory. In particular positivity
does not establish a sign for `E_even`.

### Updated signed error budget

Define `P24(phi)=sum_{|alpha|<=24}||partial^alpha phi||_1` and
`M24,T(s)=(Tq)^(-1) sum omega (1+r)^(-20) x^2(1+x)^24 exp(2s x)`.

| Term | Original support `0<s=1-kappa<1` | Restriction to `x<=m`, fixed m |
| --- | --- | --- |
| `E_even` | `O(P24 M24,T(s))` | `O_m(W P24 q)`; no vanishing conclusion. |
| `E_kernel-mix` | `O(P24 M24,T(s)/q^2)` | `O_m(W P24/q)`; tends to zero. |

The extra `q^-2` uses the odd-coefficient gap factor, not just horizontal
smallness. The complete quadratic expression is

`-(J0 ell^2/2) sum delta_j^2 D_j^2 F - i ell sum delta_j^2 K_j D_j F`,

where `D1=partial_u+partial_v`, `D2=partial_u`, `D3=partial_v`, and
`K_j=partial_delta_j J(0)` in anchor-first order. On `x<=1` its pointwise
remainder is `O(P24 x^4 (1+r)^(-20))`; on `x<=epsilon<=1`, the normalized
summed remainder is `O(W P24 q epsilon^4)`. This is not a global Taylor
approximation and does not control the complementary tuples.

### A smaller support region where kernel mixing vanishes

Let `alpha=331/4000`. For each fixed `0<s<1/8`, the existing density input
and counting lemmas give

`M24,T(s) <<_s W [q^(1+8s)(1+log q)^26 + q^28 T^(s-alpha) + q^29 T^(s-1)]`.

Divide this bound by `q^2` for the kernel-mixing error. All three terms then
tend to zero for **fixed `0<s<331/4000`** and fixed test/smoothing. The support
threshold is not claimed optimal, and its endpoint is excluded. This result
does not enlarge or silently replace the support of the original theorem.

The proof controls the weighted tail of `x` by the smaller of `O(Wq)` and
`O(W(q^2 exp(-v/4)+q^3/T))`, splitting the layer integral at `v=4 log q`.
Density applies only while `r<=T ell/2`, when all ordinates lie in
`[T/2,5T/2]`. The remaining, possibly negative or arbitrarily high partner
ordinates are handled by the global Schwartz tail. At `v=(331/1000)q` the
density estimate is frozen at its allowed endpoint, producing `T^-alpha`.

On this smaller fixed support the outstanding estimate is exactly
**`E_even=o(1)`**. Its current absolute bound grows rather than vanishes.
For the original larger class, the outstanding estimate remains
`E_even+E_kernel-mix=o(1)`. Neither statement is proved here.

## Constant-kernel replacement

The new lemma `ORDINATE-CONSTANT-KERNEL-001` removes the averaged kernel from
the remaining even error on the same smaller support. For each tuple define

`H_delta(u,v)=integral phi(xi,eta) exp(2pi i(u xi+v eta)) (prod_j cosh(a_j)-1) dxi deta`.

Evaluate that integral first, then form the absolutely convergent sums

`E_constant=c J* sum omega H_delta`,

`E_replacement=c sum omega (J_empty-J*) H_delta`,

where `c=16/(3Tq)` and `J*=3pi/8`. Exactly
`E_even=E_constant+E_replacement`. The uniform kernel estimate is

`|J_empty-J*| <= C min(a^2+d^2+sum delta_j^2,1) <= C(r^2+x^2)/q^2`

for sufficiently large T. The first inequality is uniform in all real gaps
and the closed horizontal cube, including coincident centers. The second
uses the project scaling. After Fourier integration, the factor `r^2` is
absorbed by two powers of real-plane decay, and `x^2` by the moment weight.

| Term | Bound and status |
| --- | --- |
| `E_replacement` | `O(P24 M24,T(s)/q^2)` for the original support class; o(1) for fixed `0<s<331/4000`. |
| `E_constant` | Exactly `(2pi/(Tq)) sum omega [F(z21,z31)-F(u,v)]`; vanishing remains **open**. |

For fixed `0<s<1/8`, the explicit replacement bound is

`|E_replacement| <<_s W P24 [q^(-1+8s)(1+log q)^26 + q^26 T^(s-331/4000) + q^27 T^(s-1)]`.

No endpoint extension to `s=331/4000` is made. On the smaller fixed support,
the ordinate-only asymptotic is equivalent to **`E_constant=o(1)`**.
For the original larger class the exact remaining error is
`E_constant+E_replacement+E_kernel-mix`.

### Convergence convention after removing the kernel

The constant-kernel sum is a sum of evaluated tuple integrals. Their bound
`C P24 x^2(1+x)^22 exp(2s x) (1+r)^(-22)` and the unit zero counts prove
absolute convergence at fixed T. The same holds for each reflected test
difference in the finite cosh expansion. Independent reflection-invariant
ordinate cutoffs may then be removed separately, giving the exact kernel-free
zero-sum representation and retaining all multiplicities and diagonals.

The kernel-free formula makes **no assertion of absolute interchange** of the
infinite zero sum with the unevaluated Fourier integral. All cutoff limits
precede the height limit; test, smoothing and support margin remain fixed.

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

The seventeen exact regression checks cover telescoping signs, normalization,
reflection with multiplicities and index partitions, colliding centers,
closed horizontal parameter endpoints, support-sector identities, finite
count majorization and microscopic sensitivity. They do not verify analytic
asymptotics. Polynomial and mode fixtures are used for finite identities
only, and are not passed off as admissible Schwartz tests. The full triple
test discovery also includes these checks; the existing PDF harness still
builds the weighted baseline manuscript. The six cancellation checks add the
eight-reflection expansion, coefficient parity and gap reflection, scalar
positivity, the failure of independent reflection to preserve index diagonals,
the full quadratic coefficient via exact series division, and the density
exponents including the excluded support endpoint.
The three constant-kernel checks cover the exact splitting and normalization
at degenerate tuples, the kernel's quadratic expansion at the full origin,
and the kernel-free reindexing identity with independent ordinate cutoffs and
repeated occurrences. These remain finite algebra checks, not convergence
or asymptotic certificates.

Initial reduction validation on 2026-10-03 (Python 3.12.3): all 70 pair tests and 117 triple
tests passed. The separate six-page reduction PDF compiled with no remaining
warnings or unresolved references. Both historical audit validators passed;
the old claim blocks and archived baseline remained unchanged. This was a
development-worktree validation, not a newly archived clean-checkout baseline.

Cancellation-extension validation on 2026-10-03: all **70 pair tests and
123 triple tests** passed, including 14 ordinate-extension checks. The revised
**10-page PDF** compiled without warnings or unresolved references. Both
historical audit validators passed after the documented append-only ledger
review. This remains development-worktree validation; no new clean-checkout
archive or analytic proof certificate is claimed.

Constant-kernel validation on 2026-10-05: all **70 pair tests and 126 triple
tests** passed, including 17 ordinate-extension checks. The revised
**11-page PDF** compiled without warnings or unresolved references. Both
historical audit validators passed after verification that every prior claim
block was unchanged. The weighted manuscript, dependency graph and archived
baseline were untouched. This was a development-worktree run, not a new
clean-checkout archive or an analytic proof certificate.

## Remaining research step

Prove `E_constant=o(1)` first on a fixed region `h<=s<331/4000`, or find an
alternative ordinate-only argument. This would establish the target on a
nonempty support region. The original larger class still requires the full
signed sum to vanish. Density at unscaled horizontal distances is
insufficient for the present continuity argument; see
[the recorded failed inference](dead-ends.md#ordinate-transfer-at-microscopic-horizontal-distance).
There is no proof here that the target is impossible or equivalent to RH.
