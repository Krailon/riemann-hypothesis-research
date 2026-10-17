import HigherCorrelations.PairPrimeMeanDefinitions
import Mathlib.Analysis.Complex.ExponentialBounds

/-! UNCONDITIONAL. The chosen bandwidth is admissible on the closed parameter range. -/
namespace HigherCorrelations
noncomputable section

theorem pairPrimeMean_log_bounds (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    0 < Real.log (2*X) ∧ Real.log (2*X) ≤ X ∧ X ≤ T*Real.log (2*X) := by
  have hX0 : 0 < X := by linarith
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hl3 : 1 ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hlo : Real.log 2 ≤ Real.log (2*X) := Real.log_le_log (by norm_num) (by linarith)
  refine ⟨by linarith, ?_, ?_⟩
  · rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hX0.ne']
    linarith [Real.log_le_sub_one_of_pos hX0]
  · by_cases hx : X ≤ 3/2
    · nlinarith
    · have hl := Real.log_le_log (by norm_num : (0:ℝ)<3) (by linarith : 3 ≤ 2*X)
      nlinarith

theorem pairPrimeMeanBandwidth_pos (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    0 < pairPrimeMeanBandwidth X T := by
  have hl : 0 < Real.log (2*X) := Real.log_pos (by linarith)
  unfold pairPrimeMeanBandwidth
  positivity

theorem pairPrimeMeanBandwidth_admissible (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    1/(2*T) ≤ pairPrimeMeanBandwidth X T ∧ pairPrimeMeanBandwidth X T ≤ 1/2 := by
  obtain ⟨hl,hlX,hlT⟩ := pairPrimeMean_log_bounds X T hX hT hXT
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith
  have hq : 0 ≤ Real.log (2*X)/(T*X) := by positivity
  have hs := Real.sq_sqrt hq
  have hs0 := Real.sqrt_nonneg (Real.log (2*X)/(T*X))
  have hlo : 1/T^2 ≤ Real.log (2*X)/(T*X) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlT hT0.le]
  have hhi : Real.log (2*X)/(T*X) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hslo : 1/T ≤ Real.sqrt (Real.log (2*X)/(T*X)) := by
    have he : (1/T)^2 = 1/T^2 := by ring
    have hp : 0 < 1/T := by positivity
    nlinarith
  unfold pairPrimeMeanBandwidth
  constructor
  · have he : 1/(2*T) = (1/2)*(1/T) := by ring
    rw [he]; linarith
  · nlinarith

/-- Exact balancing identities; no asymptotic simplification is used. -/
theorem pairPrimeMeanBandwidth_balance (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    Real.log (2*X)/pairPrimeMeanBandwidth X T = 2*Real.sqrt (T*X*Real.log (2*X)) ∧
    T*pairPrimeMeanBandwidth X T*X = Real.sqrt (T*X*Real.log (2*X))/2 := by
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith
  have hl : 0 < Real.log (2*X) := Real.log_pos (by linarith)
  have hA : 0 < Real.sqrt (T*X) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < Real.sqrt (Real.log (2*X)) := Real.sqrt_pos.mpr hl
  have hs := Real.sq_sqrt (show 0 ≤ T*X by positivity)
  have ht := Real.sq_sqrt hl.le
  unfold pairPrimeMeanBandwidth
  rw [Real.sqrt_div hl.le,Real.sqrt_mul (show 0 ≤ T*X by positivity)]
  constructor <;> field_simp <;> nlinarith

end
end HigherCorrelations
