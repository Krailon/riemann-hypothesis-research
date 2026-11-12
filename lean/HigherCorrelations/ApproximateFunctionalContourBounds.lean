import HigherCorrelations.ApproximateFunctionalDefinitions
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! UNCONDITIONAL contour-denominator separation. The proof uses the principal
logarithm only locally near 1 and recovers the integer winding explicitly.
It is uniform in the height and avoids a numerical minimum search. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem afe_exp_near_lattice (z : ℂ) (hz : ‖exp z-1‖ ≤ 1/2) :
    ∃ n : ℤ, ‖z - n*(2*(Real.pi:ℂ)*I)‖ ≤ (3/2)*‖exp z-1‖ := by
  have hlog := Complex.norm_log_one_add_half_le_self hz
  rw [show 1+(exp z-1)=exp z by ring] at hlog
  obtain ⟨n,hn⟩ := exp_eq_exp_iff_exists_int.mp (exp_log (exp_ne_zero z)).symm
  refine ⟨n, ?_⟩
  have he : z-n*(2*(Real.pi:ℂ)*I) = log (exp z) := by linear_combination hn
  rw [he]
  exact hlog

theorem afe_exp_sub_one_lower (z : ℂ) (r : ℝ)
    (hsep : ∀ n : ℤ, r ≤ ‖z-n*(2*(Real.pi:ℂ)*I)‖) :
    min (1/2 : ℝ) (2*r/3) ≤ ‖exp z-1‖ := by
  by_cases hz : ‖exp z-1‖ ≤ 1/2
  · obtain ⟨n,hn⟩ := afe_exp_near_lattice z hz
    have h := (hsep n).trans hn
    exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (le_of_lt (lt_of_not_ge hz))

theorem afe_contour_denominator (z : ℂ)
    (hsep : ∀ n : ℤ, (1/4 : ℝ) ≤ ‖z-n*(2*(Real.pi:ℂ)*I)‖) :
    1/6 ≤ ‖exp z-1‖ := by
  have h := afe_exp_sub_one_lower z (1/4) hsep
  norm_num at h ⊢
  exact h

theorem afe_contour_inverse_bound (z : ℂ)
    (hsep : ∀ n : ℤ, (1/4 : ℝ) ≤ ‖z-n*(2*(Real.pi:ℂ)*I)‖) :
    ‖(exp z-1)⁻¹‖ ≤ 6 := by
  rw [norm_inv]
  have h := afe_contour_denominator z hsep
  have := inv_anti₀ (by norm_num : (0:ℝ)<1/6) h
  norm_num at this
  exact this

theorem afe_floor_ratio {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ x ≤ 2*(⌊x⌋₊ : ℝ) := by
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hx)
  have hnr : (1:ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hlt := Nat.lt_floor_add_one x
  exact ⟨hn, by linarith⟩

/-- Fixed contour parameters r₀=λ₀=c=1/4 and d=4 meet the four
admissibility conditions of the source's Theorem 6, with t₀=2π. -/
theorem afe_contour_parameters (σ τ x y : ℝ)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (hτ : 2*Real.pi ≤ τ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : 2*Real.pi*x*y = τ) :
    (0:ℝ) < 1/4 ∧ 1/4 ≤ Real.pi/Real.sqrt 2 ∧
    (1/4)*x/τ ≤ 1/4 ∧
    (1/4:ℝ) ≤ 3*Real.sqrt 2/(10+4*(1-σ)/(2*Real.pi)) ∧
    (1/4:ℝ) ≤ (1/4)*τ/x ∧
    Real.pi*x/(2*(⌊x⌋₊ : ℝ)) ≤ 4 := by
  have hp := Real.pi_gt_three
  have hp' := Real.pi_lt_four
  have hτpos : 0 < τ := by linarith
  have hxpos : 0 < x := by linarith
  have hsqrt : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hsqrt' : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have hxt : x ≤ τ := by
    have hb := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2*Real.pi*x by positivity)
    nlinarith
  have hdenpos : 0 < 10+4*(1-σ)/(2*Real.pi) := by positivity
  have hsmall : 4*(1-σ)/(2*Real.pi) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    linarith
  obtain ⟨hn,hn'⟩ := afe_floor_ratio hx
  have hnpos : (0:ℝ) < ⌊x⌋₊ := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  · apply (div_le_iff₀ hτpos).mpr
    linarith
  · apply (le_div_iff₀ hdenpos).mpr
    linarith
  · apply (le_div_iff₀ hxpos).mpr
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 2*(⌊x⌋₊:ℝ))).mpr
    have := mul_le_mul_of_nonneg_left hn' Real.pi_pos.le
    nlinarith

end
end HigherCorrelations
