import HigherCorrelations.ProfileZeroGapDefinitions
import HigherCorrelations.ProfileMicroscopicLimits

/-! UNCONDITIONAL explicit zero-gap horizontal dependence on the closed cube.
All boundary points and coincidences are included. The microscopic limit keeps
all three horizontal parameters; no zero sum is interchanged with this limit. -/
namespace HigherCorrelations
noncomputable section
open Filter Set
open scoped Topology

theorem zeroGapHorizontal_differences (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    |e-f|≤1 ∧ |e+g|≤1 ∧ |f+g|≤1 := by
  exact ⟨(abs_sub e f).trans (by linarith),
    (abs_add_le e g).trans (by linarith), (abs_add_le f g).trans (by linarith)⟩

theorem zeroGapHorizontal_factor_bounds (h : ℝ) (hh : |h|≤1) :
    3≤4-h^2 ∧ 4-h^2≤4 := by
  rcases abs_le.mp hh with ⟨hl,hu⟩
  constructor <;> nlinarith [sq_nonneg h]

theorem zeroGapHorizontal_factor_pos (h : ℝ) (hh : |h|≤1) : 0<4-h^2 :=
  lt_of_lt_of_le (by norm_num) (zeroGapHorizontal_factor_bounds h hh).1

theorem zeroGapHorizontal_factor_ne_zero (h : ℝ) (hh : |h|≤1) : 4-h^2≠0 :=
  (zeroGapHorizontal_factor_pos h hh).ne'

theorem zeroGapHorizontalDenominator_bounds (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    27≤zeroGapHorizontalDenominator e f g ∧ zeroGapHorizontalDenominator e f g≤64 := by
  obtain ⟨ha,hb,hc⟩ := zeroGapHorizontal_differences e f g he hf hg
  obtain ⟨ha0,ha1⟩ := zeroGapHorizontal_factor_bounds (e-f) ha
  obtain ⟨hb0,hb1⟩ := zeroGapHorizontal_factor_bounds (e+g) hb
  obtain ⟨hc0,hc1⟩ := zeroGapHorizontal_factor_bounds (f+g) hc
  constructor
  · calc
      (27:ℝ) = 3*3*3 := by norm_num
      _ ≤ zeroGapHorizontalDenominator e f g := by unfold zeroGapHorizontalDenominator; gcongr
  · calc
      zeroGapHorizontalDenominator e f g ≤ 4*4*4 := by unfold zeroGapHorizontalDenominator; gcongr
      _ = 64 := by norm_num

theorem zeroGapHorizontalDenominator_pos (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    0<zeroGapHorizontalDenominator e f g :=
  lt_of_lt_of_le (by norm_num) (zeroGapHorizontalDenominator_bounds e f g he hf hg).1

theorem zeroGapHorizontalDenominator_ne_zero (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    zeroGapHorizontalDenominator e f g≠0 :=
  (zeroGapHorizontalDenominator_pos e f g he hf hg).ne'

theorem zeroGapHorizontal_numerator_lower (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    21≤24-(e-f)^2-(e+g)^2-(f+g)^2 := by
  obtain ⟨ha,hb,hc⟩ := zeroGapHorizontal_differences e f g he hf hg
  have h1 := (zeroGapHorizontal_factor_bounds (e-f) ha).1
  have h2 := (zeroGapHorizontal_factor_bounds (e+g) hb).1
  have h3 := (zeroGapHorizontal_factor_bounds (f+g) hc).1
  linarith

theorem zeroGapHorizontalProfile_pos (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    0<zeroGapHorizontalProfile e f g := by
  unfold zeroGapHorizontalProfile
  apply div_pos (mul_pos Real.pi_pos _) (zeroGapHorizontalDenominator_pos e f g he hf hg)
  exact lt_of_lt_of_le (by norm_num) (zeroGapHorizontal_numerator_lower e f g he hf hg)

private theorem zero_gap_square (h : ℝ) : (-(Complex.I*(h:ℂ)))^2=-((h^2:ℝ):ℂ) := by
  push_cast
  simp [mul_pow,Complex.I_sq]

theorem rationalProfile_zero_gap_horizontal (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    rationalProfile 0 0 e f g=(zeroGapHorizontalProfile e f g:ℂ) := by
  unfold rationalProfile rationalKernel zeroGapHorizontalProfile zeroGapHorizontalDenominator
  push_cast
  have h1 : (0-Complex.I*(e:ℂ))-(0-Complex.I*f)=-(Complex.I*((e-f:ℝ):ℂ)) := by push_cast; ring
  have h2 : (0-Complex.I*(e:ℂ))-Complex.I*g=-(Complex.I*((e+g:ℝ):ℂ)) := by push_cast; ring
  have h3 : (0-Complex.I*(f:ℂ))-Complex.I*g=-(Complex.I*((f+g:ℝ):ℂ)) := by push_cast; ring
  rw [h1,h2,h3,zero_gap_square,zero_gap_square,zero_gap_square]
  push_cast
  ring

theorem zeroGapHorizontalProfile_swap (e f g : ℝ) :
    zeroGapHorizontalProfile e f g=zeroGapHorizontalProfile f e g := by
  unfold zeroGapHorizontalProfile zeroGapHorizontalDenominator
  congr 1 <;> ring

theorem zeroGapHorizontalProfile_reflection (e f g : ℝ) :
    zeroGapHorizontalProfile (-e) (-f) (-g)=zeroGapHorizontalProfile e f g := by
  unfold zeroGapHorizontalProfile zeroGapHorizontalDenominator
  congr 1 <;> ring

theorem zeroGapHorizontalProfile_origin : zeroGapHorizontalProfile 0 0 0=3*Real.pi/8 := by
  unfold zeroGapHorizontalProfile zeroGapHorizontalDenominator
  ring

theorem zeroGapHorizontalProfile_cancelling (d : ℝ) :
    zeroGapHorizontalProfile d d (-d)=3*Real.pi/8 := by
  simp [zeroGapHorizontalProfile,zeroGapHorizontalDenominator]
  ring

theorem zeroGapHorizontalProfile_aligned (d : ℝ) (hd : |d|≤1/2) :
    zeroGapHorizontalProfile d d d=Real.pi*(3-d^2)/(8*(1-d^2)^2) := by
  have hd2 : d^2≤1/4 := by rcases abs_le.mp hd with ⟨hl,hu⟩; nlinarith
  have h1 : 1-d^2≠0 := by nlinarith
  unfold zeroGapHorizontalProfile
  apply (div_eq_div_iff (zeroGapHorizontalDenominator_ne_zero d d d hd hd hd)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 h1))).mpr
  unfold zeroGapHorizontalDenominator
  ring

theorem zeroGapHorizontalProfile_quarter :
    zeroGapHorizontalProfile (1/4) (1/4) (1/4)=94*Real.pi/225 := by
  norm_num [zeroGapHorizontalProfile,zeroGapHorizontalDenominator]
  ring

theorem zeroGapHorizontalProfile_quarter_ne_origin :
    zeroGapHorizontalProfile (1/4) (1/4) (1/4)≠zeroGapHorizontalProfile 0 0 0 := by
  rw [zeroGapHorizontalProfile_quarter,zeroGapHorizontalProfile_origin]
  nlinarith [Real.pi_pos]

theorem zeroGapHorizontalProfile_corners (s t r : Bool) :
    zeroGapHorizontalProfile (if s then (1/2:ℝ) else -1/2)
      (if t then (1/2:ℝ) else -1/2) (if r then (1/2:ℝ) else -1/2) =
      if s=t ∧ t≠r then 3*Real.pi/8 else 11*Real.pi/18 := by
  cases s <;> cases t <;> cases r <;>
    norm_num [zeroGapHorizontalProfile,zeroGapHorizontalDenominator] <;> ring

theorem rationalProfile_zero_gap_scaled_bound (R ℓ u v e f g : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/ℓ) (v/ℓ) e f g-(zeroGapHorizontalProfile e f g:ℂ)‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ := by
  rw [← rationalProfile_zero_gap_horizontal e f g he hf hg]
  exact rationalProfile_scaled_gap_bound R ℓ u v e f g hR hℓ hu hv he hf hg

theorem rationalProfile_zero_gap_microscopic_bound (R T u v e f g : ℝ) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (hu : |u|≤R) (hv : |v|≤R)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/meanSpacing T) (v/meanSpacing T) e f g-(zeroGapHorizontalProfile e f g:ℂ)‖ ≤
      (16*Real.pi*R*(R+1)/9)/meanSpacing T := by
  rw [← rationalProfile_zero_gap_horizontal e f g he hf hg]
  exact rationalProfile_microscopic_bound R T u v e f g hR hT hu hv he hf hg

theorem rationalProfile_zero_gap_tendstoUniformlyOn (R : ℝ) (hR : 0≤R) :
    TendstoUniformlyOn
      (fun T (p : Fin 5 → ℝ) => rationalProfile (p 0/meanSpacing T) (p 1/meanSpacing T) (p 2) (p 3) (p 4))
      (fun p => (zeroGapHorizontalProfile (p 2) (p 3) (p 4):ℂ)) atTop (profileMicroscopicBox R) := by
  have hlim : Tendsto (fun T => (16*Real.pi*R*(R+1)/9)/meanSpacing T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop microscopic_meanSpacing_tendsto
  apply tripleBoundary_uniform_of_envelope _ _ _ _ hlim
  filter_upwards [eventually_ge_atTop (2*Real.pi*Real.exp (2*Real.pi))] with T hT
  intro p hp
  exact rationalProfile_zero_gap_microscopic_bound R T (p 0) (p 1) (p 2) (p 3) (p 4) hR hT
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2

end
end HigherCorrelations
