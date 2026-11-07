# Sine benchmark formalization

Assumptions: `UNCONDITIONAL`. The checked milestones cover `TRIPLE-SINE-MEASURE-001`: interval geometry,
sinc Fourier pairings, five-partition benchmark and ordinary/factorial cumulants.

For the closed interval I=[-1/2,1/2], the overlap is
I ∩ (ξ+I) ∩ (-η+I). Its endpoints are
max(0,ξ,-η)-1/2 and min(0,ξ,-η)+1/2. The span of the centers
0, ξ, -η equals the existing signedGauge(ξ,η)=max(|ξ|,|η|,|ξ+η|).
Consequently its Lebesgue measure is ENNReal.ofReal(1-signedGauge), and
its real length is max(0,1-signedGauge). This expression is named sineCycleDensity; the subsequent Fourier milestone
identifies its inverse transform with the sinc cycle.

The intersection is nonempty exactly when signedGauge≤1, is a singleton
when signedGauge=1, and is empty when signedGauge>1. Its length is positive
exactly when signedGauge<1. Closed endpoints therefore require no exclusions.
The three seams, repeated centers, origin, all six closed frequency sectors,
and explicit interior, touching and exterior examples are checked.

The product 1_I(d)1_I(ξ-d)1_I(η+d) equals the overlap indicator pointwise.
The overlap is measurable and has finite measure, proving integrability of
this real product before identifying its Bochner integral with its length.
All variables are arbitrary real numbers; there is no limiting parameter,
zero sum, or interchange of integrals in this milestone. The sign -η in the
translated third interval is essential to the ξ+η support gauge.

## Verification

Run:

```sh
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-sine-measure-only
```

The focused suite now checks all 125 public statements in 20 modules against
definition-only contracts. Twenty-two unfinished-proof rejection controls cover
the earlier geometry and sinc pairings, continuous marginals, constant-line
slices, weighted line duality, all five Fourier rows, the assembled benchmark,
tempered realization, ordinary/factorial cumulants, closed-hexagon cancellation
and moment-cumulant subtraction.
The standard combined project build, full axiom report, coverage, harness,
control-pool and pair/triple regressions also run. Allowed axioms remain
propext, Quot.sound and Classical.choice; nanoda remains disabled. The
rejection controls use the existing default four-worker pool.

The analytic coverage table records complete coverage of the historical
TRIPLE-SINE-MEASURE-001 statement through its checked components. Its historical
ledger status remains unchanged; a companion formal entry records this milestone.
The main-term comparison remains a subsequent task. No extension of the
zeta theorem from strict interior support to its boundary is claimed.
Formal ledger entries are appended only after successful verification;
historical claim blocks, dependency graph and RH audit scope are preserved.

## Sinc Fourier pairing

Put s(x)=Real.sinc(pi*x), C(u,v)=s(u)s(v)s(u-v), and
c(xi,eta)=max(0,1-max(|xi|,|eta|,|xi+eta|)). The existing pairMeanSinc
and pairMeanTriangle are reused, including the removable value s(0)=1.
The new interfaces sineCyclePlane and sineDensityPlane use the existing
FourierPlane and its measure-preserving planeCoords convention.

For every complex Schwartz F on the full plane, with the negative-forward
2pi Fourier transform, the checked bilinear identities are

    integral F C = integral (Fourier F) c,
    integral (inverseFourier phi) C = integral phi c.

There is no complex conjugation, symmetry requirement on the test, or
restriction on its Fourier support. Both physical and frequency integrands
are absolutely integrable, including when the test is replaced by its
Fourier or inverse Fourier transform. The matching one-dimensional identity
integral F s^2 = integral (Fourier F) tau and its inverse-test form are
checked using the earlier pair-diagonal squared-sinc machinery.

The new analytic input is the pointwise inverse transform of c. Write its
parameter integrand as B(d)B(xi-d)B(eta+d) exp(2pi i (u xi+v eta)), where
B=1_I. Its norm is bounded by the indicator of I times [-1,1]^2.
This explicit compact majorant and measurability prove integrability before
Fubini interchanges d with (xi,eta). The translations xi=a+d, eta=b-d
preserve Lebesgue measure. The resulting product of three one-dimensional
box transforms is exactly s(u)s(v)s(u-v). The established coordinate bridge
then gives inverseFourier c=C on FourierPlane. Reflection gives Fourier c=C.
Fourier duality for integrable functions yields the unrestricted Schwartz
pairings, using |C|<=1 and 0<=c<=1 to prove weighted absolute convergence.

The checks include all zero arguments, the three cycle axes, simultaneous
reflection, and integral c=1. The previously checked closed-overlap boundary
continues to apply. No asymptotic limit or infinite zero sum is involved.

## Five-partition benchmark and cumulants

The benchmark uses the existing TriplePattern as occurrence-index partition
labels. They impose no equality or simplicity condition on actual zeta zeros.
The mappings in relative coordinates (u,v) are:

| Pattern | Physical contribution |
| --- | --- |
| allEqual | F(0,0) |
| only01 | integral F(0,r) R2(r) dr |
| only02 | integral F(r,0) R2(r) dr |
| only12 | integral F(r,r) R2(r) dr |
| allDistinct | integral F(u,v) R3(u,v) du dv |

R2=1-s^2. The exact 3-by-3 determinant expansion gives
R3=1-s(u)^2-s(v)^2-s(u-v)^2+2C(u,v). The five-term functional,
its manuscript single-line-integral form and every Fourier row are checked.
All physical and spectral integrals are absolutely convergent.

For m=1-tau and g=1-tau(xi)-tau(eta)-tau(xi+eta)+2c, the transform is

    Fourier M3 = delta00 + m(xi)delta(eta) + m(eta)delta(xi)
                 + m(xi)delta(xi+eta) + g.

The line measures use coordinate dr throughout. The third frequency line is
(r,-r), without an arclength multiplier. The physical origin atom transforms
to constant planar density one; the constant planar density transforms to
an origin atom. All pairings are complex bilinear, without conjugation or
restrictions on the Schwartz test.

The constant-line transform uses continuous L1 marginals of plane Schwartz
functions. A seminorm bound gives an integrable majorant independent of the
other coordinate. Fourier inversion is applied only after the marginal and
its transform are proved integrable. The swap/shear/reflection coordinate maps
preserve Lebesgue measure. Weighted line transforms use integrable Fourier
duality directly, with the previously checked squared-sinc and triangle transforms.

Bounded planar densities are realized as L-infinity tempered distributions;
weighted line distributions compose their one-dimensional counterparts with
continuous Schwartz restriction maps. All five rows, the assembled benchmark,
covariance lifts, and both cumulants have checked tempered realizations.
Continuity of the benchmark and cumulant functionals is explicit.

The ordinary covariance lifts are delta minus squared sinc in each of u, v
and u-v. The checked moment-cumulant identity is

    M3 = 1 + c2(u) + c2(v) + c2(u-v) + C3ord.

Here C3ord is the origin atom minus the three squared-sinc-weighted line
measures plus 2C; its transform is g. The factorial connected subtraction
R3-R2(u)-R2(v)-R2(u-v)+2 equals 2C, whose transform is 2c.
The ordinary/factorial distinction is therefore part of the proof.

The half-sum gauge identity proves g=0 for every h<=1, including seams and
vertices. Outside that hexagon g(3/4,3/4)=1/2. The factorial density is
strictly positive for h<1 and is two at the origin. No zeta support-boundary
extension, zero-sum limit, or main-term comparison follows from this benchmark
calculation alone. Historical proof drafts, review scope and dependency graph
remain unchanged; the new formal ledger entry is append-only.
