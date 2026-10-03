# Main-term comparison with the sine benchmark

Task: proof and bookkeeping. Status: **proved-draft**. Assumptions:
`UNCONDITIONAL`; the correlation comparison additionally assumes
`SUPPORT(h<=1-kappa, 0<kappa<1)` and the existing smoothing hypotheses.
Here `h=max(|xi|,|eta|,|xi+eta|)`.

The [proof](../proofs/triple_explicit_formula.tex) and
[ledger](theorem-ledger.yaml) contain two new claims:

- **TRIPLE-SINE-MEASURE-001**, label **lem:triple-sine-measure**:
  a deterministic identity of tempered distributions, including all five
  occurrence-index partitions and the ordinary-cumulant cancellation.
- **TRIPLE-MAIN-TERM-COMPARISON-001**, label
  **lem:triple-main-term-comparison**: exact identification of the existing
  limiting functional and its two weighted asymptotic consequences.

## Benchmark and partitions

Write `s(x)=sin(pi*x)/(pi*x)`, with `s(0)=1`, and
\[
R_2(r)=1-s(r)^2,\qquad
R_3(u,v)=1-s(u)^2-s(v)^2-s(u-v)^2+2s(u)s(v)s(u-v).
\]
The latter is the three-by-three unit-density sine determinant. Set
\[
\mathcal S_3[F]=\iint F R_3+
\int R_2(r)[F(0,r)+F(r,0)+F(r,r)]\,dr+F(0,0).
\]
All integrals are absolutely convergent for Schwartz `F`. This is the
all-ordered benchmark; using just the determinant would omit main terms.
Let `tau(r)=(1-|r|)_+`, `c(xi,eta)=(1-h)_+`, `m=1-tau`.

| Index partition | Physical measure | Negative-forward Fourier transform |
| --- | --- | --- |
| `123` | `delta_(0,0)` | constant planar density `1` |
| `12\|3` | `delta(u) R_2(v)` | `delta(eta)-tau(eta)` |
| `13\|2` | `delta(v) R_2(u)` | `delta(xi)-tau(xi)` |
| `23\|1` | `delta(u-v) R_2(u)` | `delta(xi+eta)-tau(xi+eta)` |
| `1\|2\|3` | `R_3(u,v) du dv` | `delta_(0,0)-tau(xi)delta(eta)-tau(eta)delta(xi)-tau(xi)delta(xi+eta)+2c` |

Line measures use the displayed coordinate `dr`, not arclength; in
particular `delta(xi+eta)` pairs with `phi(r,-r)` with coefficient one.
The physical all-equal atom and the frequency origin atom have different
origins. The latter comes from the constant physical density in `R_3`.
Partitions refer to equality of indices. Unequal zeta occurrence indices
can still have equal complex zeros or equal ordinates. This comparison
makes no simplicity assertion.

The transform of the whole measure is
\[
\widehat M_3=\delta_{00}+m(\xi)\delta(\eta)+m(\eta)\delta(\xi)
+m(\xi)\delta(\xi+\eta)+g(\xi,\eta),
\]
\[
g=1-\tau(\xi)-\tau(\eta)-\tau(\xi+\eta)+2(1-h)_+.
\]
To obtain the cycle transform directly, put `I=[-1/2,1/2]` and use
\[
\widehat{s(u)s(v)s(u-v)}=|I\cap(\xi+I)\cap(-\eta+I)|=(1-h)_+.
\]
The proof justifies this on Schwartz tests by Fubini over three compact
intervals with majorant `|F(u,v)|`. Since
`|xi|+|eta|+|xi+eta|=2h`, the planar density `g` vanishes for `h<=1`,
including every internal axis and the outer boundary. It does not vanish
globally: `g(3/4,3/4)=1/2`.

## Exact comparison and retained errors

For arbitrary complex `phi` smooth and compactly supported in `h<1`,
let `F` be its positive-inverse Fourier transform. Distribution pairings
are bilinear: `S_3[F]=<Fourier(M_3),phi(-.)>`. Central evenness of the
measure permits replacing `phi(-.)` by `phi`; no complex conjugation or
evenness assumption on the test is needed. Consequently
\[
\mathcal S_3[F]=\phi(0,0)+\int |r|
[\phi(r,0)+\phi(0,r)+\phi(r,-r)]\,dr,
\qquad \mathcal A[\phi]=\tfrac32\mathcal S_3[F].
\]
With `B=T/(2pi)`, `b=log B`, `q=log T`, `L=log(2T+2)`, define
\[
\mathfrak E_{\rm signed}=\|\phi\|_{C^1}(1+W_\infty+W_1)
[b^{-1}+B^{-\kappa}L^3],\qquad
\mathfrak E_{\rm kernel}=\|\phi\|_1(W_\infty+W'_\infty)B^{-\kappa}L^3.
\]
Here `W_1=||omega'||_1` and `W'_inf=||omega'||_inf` remain distinct.
The existing [signed-test theorem](triple-test-functions.md) and
[kernel localization](triple-kernel.md) now read
\[
\mathcal A_T[\phi]=\tfrac32\mathcal S_3[F]+O(\mathfrak E_{\rm signed}),
\qquad
\mathcal A_T^{\mathcal J}[\phi]=\tfrac32\mathcal S_3[F]
+O(\mathfrak E_{\rm signed}+\mathfrak E_{\rm kernel}).
\]
These hold for `T>=2pi e` and support in `h<=1-kappa`, `0<kappa<1`,
with effective absolute constants inherited unchanged. No new analytic
error enters the comparison. Fix test, margin and smoothing before
`T -> infinity`; varying families must make both errors vanish.

| Convention | Exact translation |
| --- | --- |
| Forward transform | negative exponential `exp(-2pi i x.xi)` |
| Inverse transform | positive exponential, bilinear pairing without conjugation |
| Anchor differences | `(u,v)=(x2-x1,x3-x1)` |
| Positive-inverse three-frequency vector | `(-xi-eta,xi,eta)` |
| Negative-exponential source vector | `(xi+eta,-xi,-eta)` |
| Three-frequency support size | `sum |lambda_j|=2h`; project margin gives `<=2-2kappa` |
| Outer support endpoints | deterministic cancellation includes `h=1`; zeta theorem still requires compact support in `h<1` |
| Native statistic normalization | `A_T=(8/q) sum K_T F(z21,z31)` |
| Profile normalization | `A_T^J=(8/(Tq)) sum omega J F(z21,z31)` |
| Local critical profile | `3pi/8`; exact finite-height factor relative to `1/(T L_T)` is `3b/(2q)` |
| Limiting main functional | `(3/2) S_3[F]`; multiplying the weighted observable by `2/3` normalizes its limit |

## What the cumulant cancellation means

The reduced ordinary covariance is `c_2(x)=delta_0(x)-s(x)^2`.
Subtract `1+c_2(u)+c_2(v)+c_2(u-v)` from `M_3`. The ordinary third
cumulant is
\[
C_3^{\rm ord}=\delta_{00}-\delta(u)s(v)^2-\delta(v)s(u)^2
-\delta(u-v)s(u)^2+2s(u)s(v)s(u-v),
\]
and its transform is exactly `g`. Thus the **ordinary benchmark cumulant**
vanishes on tests supported in the hexagon. The factorial third cumulant
is the cycle alone, with transform `2c`, and is nonzero there.

The new result identifies the main term of the unconditional weighted
full-zero statistic. Its complex test arguments, horizontal dependence,
and kernel remain present. Constant-kernel replacement and an ordinary
unweighted zeta correlation still need additional work. A corresponding
weighted zeta cumulant also requires compatible lower-order weighted
statistics before subtraction. No new horizontal consequence or completion
of Work Package B is asserted.

## Provenance and checks

The [source note](literature-notes/triple-sine-comparison.md) records the
consulted author manuscript and the limited use of its unitary determinant
conventions. Both new claims are proved directly in project notation.
The [exact checks](../scripts/check_triple_main_term.py) verify determinant
and partition algebra, interval overlaps, support and sign conventions,
cumulant subtraction and normalization. They are verification, not an
analytic proof or a numerical certificate.

The pair-audit ledger hash is refreshed after verifying the old ledger is
an unchanged byte prefix with only these two claims appended. Existing
Work Package A claims, audit snapshot and reproduction archive are
unchanged; the pair audit does not cover these new Work Package B claims.

Validation on 2026-10-02: all **80 triple checks** (including nine new
comparison checks) and **70 pair checks** passed. The **32-page** proof
compiled in three passes with shell escape disabled, with no final-pass
warnings, unresolved references or overfull/underfull boxes.

```bash
python3 -B -m unittest discover -s scripts -p 'check_triple_*.py'
python3 -B -m unittest discover -s scripts -p 'check_pair_*.py'
```

The [assembled theorem](triple-theorem.md) now collects this comparison
and the explicit profile in unit benchmark normalization, with every
hypothesis and both errors stated together.
