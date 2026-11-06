import HigherCorrelations.ProfileCriticalDefinitions
import HigherCorrelations.ProfileMicroscopicLimits

/-! UNCONDITIONAL critical-parameter quadratic expansion with explicit remainder.
The argument is rational algebra with positive denominators, not a formal Taylor series. -/
namespace HigherCorrelations
noncomputable section

theorem criticalGapQuadratic_nonneg (u v : ℝ) : 0≤criticalGapQuadratic u v := by
  unfold criticalGapQuadratic
  nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u-v)]

theorem criticalGapQuadratic_bound (R u v : ℝ) (hR : 0≤R)
    (hu : |u|≤R) (hv : |v|≤R) : criticalGapQuadratic u v≤3*R^2 := by
  have hu2 : u^2≤R^2 := by nlinarith [sq_abs u, (sq_le_sq₀ (abs_nonneg u) hR).mpr hu]
  have hv2 : v^2≤R^2 := by nlinarith [sq_abs v, (sq_le_sq₀ (abs_nonneg v) hR).mpr hv]
  unfold criticalGapQuadratic
  nlinarith [sq_nonneg (u+v)]

theorem criticalGapQuadratic_div (u v ℓ : ℝ) :
    criticalGapQuadratic (u/ℓ) (v/ℓ)=criticalGapQuadratic u v/ℓ^2 := by
  unfold criticalGapQuadratic
  ring

theorem criticalProfileRemainderConstant_nonneg (R : ℝ) :
    0≤criticalProfileRemainderConstant R := by
  unfold criticalProfileRemainderConstant
  positivity

theorem rationalProfile_critical_remainder_identity (a b : ℝ) :
    rationalProfile a b 0 0 0-criticalProfileApproximation 1 a b =
      ((Real.pi*((7/2:ℝ)*(criticalGapQuadratic a b)^2+
        (5/8:ℝ)*(criticalGapQuadratic a b)^3-(3/8:ℝ)*(a^2*b^2*(a-b)^2)+
        (5/32:ℝ)*criticalGapQuadratic a b*(a^2*b^2*(a-b)^2))/
        ((4+(a-b)^2)*(4+a^2)*(4+b^2)) : ℝ) : ℂ) := by
  rw [rationalProfile_real]
  unfold criticalProfileApproximation criticalGapQuadratic
  push_cast
  have ha : (4+(a:ℂ)^2)≠0 := by exact_mod_cast (show (4+a^2:ℝ)≠0 by positivity)
  have hb : (4+(b:ℂ)^2)≠0 := by exact_mod_cast (show (4+b^2:ℝ)≠0 by positivity)
  have hab : (4+((a:ℂ)-b)^2)≠0 := by exact_mod_cast (show (4+(a-b)^2:ℝ)≠0 by positivity)
  field_simp
  <;> ring

private theorem critical_remainder_real_bound (R a b : ℝ) (hR : 0≤R)
    (ha : |a|≤R) (hb : |b|≤R) :
    |Real.pi*((7/2:ℝ)*(criticalGapQuadratic a b)^2+
      (5/8:ℝ)*(criticalGapQuadratic a b)^3-(3/8:ℝ)*(a^2*b^2*(a-b)^2)+
      (5/32:ℝ)*criticalGapQuadratic a b*(a^2*b^2*(a-b)^2))/
      ((4+(a-b)^2)*(4+a^2)*(4+b^2))| ≤ criticalProfileRemainderConstant R := by
  let q := criticalGapQuadratic a b
  let p := a^2*b^2*(a-b)^2
  let D := (4+(a-b)^2)*(4+a^2)*(4+b^2)
  have hq : 0≤q := criticalGapQuadratic_nonneg a b
  have hqb : q≤3*R^2 := criticalGapQuadratic_bound R a b hR ha hb
  have hp : 0≤p := by dsimp [p]; positivity
  have ha2 : a^2≤R^2 := by nlinarith [sq_abs a, (sq_le_sq₀ (abs_nonneg a) hR).mpr ha]
  have hb2 : b^2≤R^2 := by nlinarith [sq_abs b, (sq_le_sq₀ (abs_nonneg b) hR).mpr hb]
  have hab : |a-b|≤2*R := (abs_sub a b).trans (by linarith)
  have hab2 : (a-b)^2≤(2*R)^2 := by
    nlinarith [sq_abs (a-b), (sq_le_sq₀ (abs_nonneg (a-b)) (by positivity : 0≤2*R)).mpr hab]
  have hpb : p≤4*R^6 := calc
    p ≤ R^2*R^2*(2*R)^2 := by dsimp [p]; gcongr
    _ = _ := by ring
  have hD : 64≤D := by
    calc
      (64:ℝ) = 4*4*4 := by norm_num
      _ ≤ D := by dsimp [D]; gcongr <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a-b)]
  have hn : |(7/2:ℝ)*q^2+(5/8:ℝ)*q^3-(3/8:ℝ)*p+(5/32:ℝ)*q*p| ≤
      (7/2:ℝ)*q^2+(5/8:ℝ)*q^3+(3/8:ℝ)*p+(5/32:ℝ)*q*p := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg q, mul_nonneg hq hp, pow_nonneg hq 3]
  have hn2 : (7/2:ℝ)*q^2+(5/8:ℝ)*q^3+(3/8:ℝ)*p+(5/32:ℝ)*q*p ≤
      (7/2:ℝ)*(3*R^2)^2+(5/8:ℝ)*(3*R^2)^3+(3/8:ℝ)*(4*R^6)+
        (5/32:ℝ)*(3*R^2)*(4*R^6) := by gcongr
  change |Real.pi*(_)/D|≤_
  rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (show 0<D by linarith)]
  calc
    _ ≤ Real.pi*((7/2:ℝ)*(3*R^2)^2+(5/8:ℝ)*(3*R^2)^3+(3/8:ℝ)*(4*R^6)+
        (5/32:ℝ)*(3*R^2)*(4*R^6))/64 := by
      apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hn.trans hn2) Real.pi_pos.le)
        (by norm_num) hD
    _ ≤ criticalProfileRemainderConstant R := by
      unfold criticalProfileRemainderConstant
      have h4 := pow_nonneg hR 4
      have h6 := pow_nonneg hR 6
      have h8 := pow_nonneg hR 8
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      nlinarith

theorem rationalProfile_critical_remainder_bound (R a b : ℝ) (hR : 0≤R)
    (ha : |a|≤R) (hb : |b|≤R) :
    ‖rationalProfile a b 0 0 0-criticalProfileApproximation 1 a b‖ ≤
      criticalProfileRemainderConstant R := by
  rw [rationalProfile_critical_remainder_identity,Complex.norm_real,Real.norm_eq_abs]
  exact critical_remainder_real_bound R a b hR ha hb


theorem rationalProfile_critical_scaled_bound (R ℓ u v : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/ℓ) (v/ℓ) 0 0 0-criticalProfileApproximation ℓ u v‖ ≤
      criticalProfileRemainderConstant R/ℓ^4 := by
  have hl : 0<ℓ := by linarith
  have hu' : |u/ℓ|≤R/ℓ := by rw [abs_div,abs_of_pos hl]; gcongr
  have hv' : |v/ℓ|≤R/ℓ := by rw [abs_div,abs_of_pos hl]; gcongr
  have h := rationalProfile_critical_remainder_bound (R/ℓ) (u/ℓ) (v/ℓ) (by positivity) hu' hv'
  have he : criticalProfileApproximation 1 (u/ℓ) (v/ℓ)=criticalProfileApproximation ℓ u v := by
    unfold criticalProfileApproximation
    rw [criticalGapQuadratic_div]
    congr 1
    ring
  rw [he] at h
  apply h.trans
  unfold criticalProfileRemainderConstant
  have hl6 : ℓ^4≤ℓ^6 := by gcongr <;> norm_num
  have hl8 : ℓ^4≤ℓ^8 := by gcongr <;> norm_num
  calc
    _ = Real.pi*(R^4/ℓ^4+R^6/ℓ^6+R^8/ℓ^8) := by ring
    _ ≤ Real.pi*(R^4/ℓ^4+R^6/ℓ^4+R^8/ℓ^4) := by gcongr
    _ = _ := by ring

theorem rationalProfile_critical_microscopic_bound (R T u v : ℝ) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/meanSpacing T) (v/meanSpacing T) 0 0 0-
      criticalProfileApproximation (meanSpacing T) u v‖ ≤
      criticalProfileRemainderConstant R/(meanSpacing T)^4 :=
  rationalProfile_critical_scaled_bound R (meanSpacing T) u v hR
    (microscopic_meanSpacing_ge_one T hT) hu hv

theorem rationalProfile_critical_leading_bound (R ℓ u v : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/ℓ) (v/ℓ) 0 0 0-kernelBenchmark‖ ≤
      criticalProfileLeadingConstant R/ℓ^2 := by
  have hl : 0<ℓ := by linarith
  have hq := criticalGapQuadratic_nonneg u v
  have hqb := criticalGapQuadratic_bound R u v hR hu hv
  have he : ‖criticalProfileApproximation ℓ u v-kernelBenchmark‖ =
      5*Real.pi*criticalGapQuadratic u v/(32*ℓ^2) := by
    unfold criticalProfileApproximation kernelBenchmark
    have hc : (3*(Real.pi:ℂ)/8)=((3*Real.pi/8:ℝ):ℂ) := by push_cast; ring
    rw [hc,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have hr : 3*Real.pi/8-5*Real.pi*criticalGapQuadratic u v/(32*ℓ^2)-3*Real.pi/8 =
        -(5*Real.pi*criticalGapQuadratic u v/(32*ℓ^2)) := by ring
    rw [hr,abs_neg,abs_of_nonneg (by positivity)]
  have hl4 : ℓ^2≤ℓ^4 := by gcongr <;> norm_num
  calc
    _ ≤ ‖rationalProfile (u/ℓ) (v/ℓ) 0 0 0-criticalProfileApproximation ℓ u v‖+
      ‖criticalProfileApproximation ℓ u v-kernelBenchmark‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ criticalProfileRemainderConstant R/ℓ^4+5*Real.pi*criticalGapQuadratic u v/(32*ℓ^2) := by
      rw [he]
      exact add_le_add (rationalProfile_critical_scaled_bound R ℓ u v hR hℓ hu hv) (le_refl _)
    _ ≤ criticalProfileRemainderConstant R/ℓ^2+5*Real.pi*(3*R^2)/(32*ℓ^2) := by
      gcongr
      exact criticalProfileRemainderConstant_nonneg R
    _ = criticalProfileLeadingConstant R/ℓ^2 := by unfold criticalProfileLeadingConstant; ring

theorem rationalProfile_critical_zero_radius (ℓ u v : ℝ) (hu : |u|≤0) (hv : |v|≤0) :
    rationalProfile (u/ℓ) (v/ℓ) 0 0 0=criticalProfileApproximation ℓ u v := by
  have hu0 : u=0 := abs_nonpos_iff.mp hu
  have hv0 : v=0 := abs_nonpos_iff.mp hv
  subst u; subst v
  simp [criticalProfileApproximation,criticalGapQuadratic,rationalProfile_origin,kernelBenchmark]



theorem rationalProfile_critical_coincident_bound (R ℓ u : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) :
    ‖rationalProfile (u/ℓ) (u/ℓ) 0 0 0-criticalProfileApproximation ℓ u u‖ ≤
      criticalProfileRemainderConstant R/ℓ^4 :=
  rationalProfile_critical_scaled_bound R ℓ u u hR hℓ hu hu

theorem rationalProfile_critical_scale_endpoint (R u v : ℝ) (hR : 0≤R)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile u v 0 0 0-criticalProfileApproximation 1 u v‖ ≤
      criticalProfileRemainderConstant R :=
  rationalProfile_critical_remainder_bound R u v hR hu hv

theorem rationalProfile_critical_height_endpoint (R u v : ℝ) (hR : 0≤R)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/meanSpacing (2*Real.pi*Real.exp (2*Real.pi)))
      (v/meanSpacing (2*Real.pi*Real.exp (2*Real.pi))) 0 0 0-
      criticalProfileApproximation (meanSpacing (2*Real.pi*Real.exp (2*Real.pi))) u v‖ ≤
      criticalProfileRemainderConstant R/(meanSpacing (2*Real.pi*Real.exp (2*Real.pi)))^4 :=
  rationalProfile_critical_microscopic_bound R _ u v hR (le_refl _) hu hv

theorem rationalProfile_critical_gap_endpoints (R ℓ : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ) :
    ‖rationalProfile (R/ℓ) (-R/ℓ) 0 0 0-criticalProfileApproximation ℓ R (-R)‖ ≤
      criticalProfileRemainderConstant R/ℓ^4 :=
  rationalProfile_critical_scaled_bound R ℓ R (-R) hR hℓ (by simpa [abs_of_nonneg hR])
    (by simpa [abs_of_nonneg hR])


end
end HigherCorrelations
