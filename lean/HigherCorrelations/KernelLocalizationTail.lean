import HigherCorrelations.KernelLocalizationSumDefinitions
import HigherCorrelations.KernelLocalizationCounting
import HigherCorrelations.PairLogWeight

/-! UNCONDITIONAL logarithm-squared tails. A scaled integrable profile retains
L^2/T without extracting a numerical value for an inherited absolute constant. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem localizationTailProfile_nonneg (u : ℝ) : 0≤localizationTailProfile u := by
  unfold localizationTailProfile
  positivity

theorem localizationTailProfile_integrable : Integrable localizationTailProfile := by
  have hp : Integrable (fun u : ℝ => (1+u^2)^(-(3/4:ℝ))) := by
    convert (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 3/2) (by norm_num)) using 1
    ext u
    simp [Real.norm_eq_abs, sq_abs]
    norm_num
  apply (hp.const_mul (1+(Real.log 5+8)^2)).mono'
    (Measurable.aestronglyMeasurable (by unfold localizationTailProfile; fun_prop))
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (localizationTailProfile_nonneg u)]
  let y := 1+u^2
  have hy : 1≤y := by dsimp [y]; nlinarith [sq_nonneg u]
  have hy0 : 0<y := by linarith
  have hlog := Real.log_le_log (by positivity : 0<3*|u|+2)
    (show 3*|u|+2≤5*y by dsimp [y]; nlinarith [sq_nonneg (|u|-1),sq_abs u])
  rw [Real.log_mul (by norm_num) hy0.ne'] at hlog
  have hl : Real.log y ≤ 8*y^(1/8:ℝ) := by
    have := Real.log_le_rpow_div hy0.le (by norm_num : (0:ℝ)<1/8)
    linarith
  have hpow : 1≤y^(1/8:ℝ) := Real.one_le_rpow hy (by norm_num)
  have hfive : 0≤Real.log 5 := Real.log_nonneg (by norm_num)
  have hb : Real.log (3*|u|+2)≤(Real.log 5+8)*y^(1/8:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hpow hfive]
  have hn : 0≤Real.log (3*|u|+2) := Real.log_nonneg (by nlinarith [abs_nonneg u])
  have hs := pow_le_pow_left₀ hn hb 2
  have he : (y^(1/8:ℝ))^2=y^(1/4:ℝ) := by rw [← Real.rpow_mul_natCast hy0.le]; norm_num
  rw [mul_pow, he] at hs
  have hp1 : 1≤y^(1/4:ℝ) := Real.one_le_rpow hy (by norm_num)
  have hb' : 1+Real.log (3*|u|+2)^2 ≤ (1+(Real.log 5+8)^2)*y^(1/4:ℝ) := by linarith
  change (1+Real.log (3*|u|+2)^2)/y ≤ _
  apply (div_le_div_of_nonneg_right hb' hy0.le).trans_eq
  rw [mul_div_assoc]
  have he' : y^(1/4:ℝ)/y=y^(-(3/4:ℝ)) := by
    nth_rw 2 [← Real.rpow_one y]
    rw [← Real.rpow_sub hy0]
    norm_num
  rw [he']

theorem localization_tail_scaled_bound (T c t : ℝ) (hT : 3≤T)
    (hc : c ∈ Icc T (2*T)) (ht : T< |t-c|) :
    Real.log (|t|+2)^2*ordinateKernel (t-c) ≤
      (4*Real.log (2*T+2)^2/T^2)*localizationTailProfile ((t-c)/T) := by
  have hT0 : 0<T := by linarith
  let x := (t-c)/T
  let L := Real.log (2*T+2)
  let z := Real.log (3*|x|+2)
  have hx : |t-c|=T*|x| := by dsimp [x]; rw [abs_div, abs_of_pos hT0]; field_simp
  have hx1 : 1≤|x| := by nlinarith [ht]
  have hab : |t|+2 ≤ 3*|t-c|+2 := by
    have h := abs_add_le (t-c) c
    rw [sub_add_cancel, abs_of_nonneg (show 0≤c by linarith [hc.1])] at h
    linarith [hc.2]
  have hmul : |t|+2 ≤ (2*T+2)*(3*|x|+2) := by
    rw [hx] at hab
    nlinarith [abs_nonneg x]
  have hl := Real.log_le_log (by positivity : 0 < |t|+2) hmul
  rw [Real.log_mul (by positivity) (by positivity)] at hl
  change Real.log (|t|+2) ≤ L+z at hl
  have hL : 1≤L := localization_log_ge_one T hT
  have hz : 0≤z := Real.log_nonneg (by nlinarith [abs_nonneg x])
  have hlt : 0≤Real.log (|t|+2) := Real.log_nonneg (by nlinarith [abs_nonneg t])
  have hls := pow_le_pow_left₀ hlt hl 2
  have hsq : Real.log (|t|+2)^2 ≤ 2*L^2*(1+z^2) := by
    nlinarith [sq_nonneg (L-z), mul_nonneg (by nlinarith : 0≤L^2-1) (sq_nonneg z)]
  have hxx : T^2*x^2=(t-c)^2 := by dsimp [x]; field_simp
  have hx2 : 1≤x^2 := by nlinarith [sq_abs x]
  have hk : ordinateKernel (t-c) ≤ (2/T^2)/(1+x^2) := by
    unfold ordinateKernel
    apply (div_le_div_iff₀ (by positivity : 0<1+(t-c)^2) (by positivity : 0<1+x^2)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0<T^2)).mpr
    nlinarith
  calc
    _ ≤ (2*L^2*(1+z^2))*((2/T^2)/(1+x^2)) := mul_le_mul hsq hk
      (ordinateKernel_nonneg _) (by positivity)
    _ = _ := by unfold localizationTailProfile; dsimp [L,z,x]; ring

theorem localization_scaled_profile_integrable (T c : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ => localizationTailProfile ((t-c)/T)) :=
  (localizationTailProfile_integrable.comp_div hT.ne').comp_sub_right c

theorem localization_scaled_profile_integral (T c : ℝ) (hT : 0<T) :
    (∫ t : ℝ, localizationTailProfile ((t-c)/T)) = T*∫ u : ℝ, localizationTailProfile u := by
  rw [integral_sub_right_eq_self (fun u => localizationTailProfile (u/T)) c,
    Measure.integral_comp_div, abs_of_pos hT, smul_eq_mul]


end
end HigherCorrelations
