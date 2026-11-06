# Sine-cycle interval-overlap geometry

Assumptions: `UNCONDITIONAL`. This milestone formalizes the geometric input to
`TRIPLE-SINE-MEASURE-001`, not its complete Fourier or correlation statement.

For the closed interval I=[-1/2,1/2], the overlap is
I ∩ (ξ+I) ∩ (-η+I). Its endpoints are
max(0,ξ,-η)-1/2 and min(0,ξ,-η)+1/2. The span of the centers
0, ξ, -η equals the existing signedGauge(ξ,η)=max(|ξ|,|η|,|ξ+η|).
Consequently its Lebesgue measure is ENNReal.ofReal(1-signedGauge), and
its real length is max(0,1-signedGauge). This last expression is named
sineCycleDensity as the candidate density for the subsequent Fourier proof;
the name alone makes no transform assertion.

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

The focused suite checks all 20 public statements against definition-only
contracts, with six independent unfinished-proof rejection controls for the
span, volume, integrability, integral, singleton endpoint and six-sector law.
The standard combined project build, full axiom report, coverage, harness,
control-pool and pair/triple regressions also run. Allowed axioms remain
propext, Quot.sound and Classical.choice; nanoda remains disabled. The
rejection controls use the existing default four-worker pool.

The analytic coverage table records partial coverage only. Sinc Fourier
pairing, the five-partition benchmark, cumulant identities and the ordinary
versus factorial distinction remain subsequent work. No extension of the
zeta theorem from strict interior support to its boundary is claimed.
The formal geometry ledger entry is appended only after successful verification;
historical claim blocks, dependency graph and RH audit scope are preserved.
