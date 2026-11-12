import HigherCorrelations.ApproximateFunctionalGammaPhase
import HigherCorrelations.ApproximateFunctionalCompact

/-! UNCONDITIONAL uniform replacement of the exact functional-equation factor
by the explicit oscillatory phase, including the strip and height endpoints. -/
namespace HigherCorrelations
noncomputable section
open Complex
open scoped ComplexConjugate

theorem afeChi_phase_high (σ t : ℝ) (hσ : 1/2 ≤ σ) (hσ' : σ ≤ 1) (ht : 18 ≤ t) :
    ‖pairChi (afePoint σ t)-afePhase σ t‖ ≤ 20*afeHeight t^(1/2-σ)/t := by
  have htp : 0 < t := by linarith
  let E := afeGammaVerticalError (1-σ) t
  let k := exp ((Real.pi:ℂ)*afePoint σ t*I)
  have hE : ‖E‖ ≤ 9/t := afeGammaVerticalError_bound (1-σ) t (by linarith) (by linarith) (by linarith)
  have hEsmall : ‖E‖ ≤ 1 := hE.trans ((div_le_one htp).mpr (by linarith))
  have he : ‖exp E-1‖ ≤ 18/t := by
    apply (Complex.norm_exp_sub_one_le hEsmall).trans
    calc
      _ ≤ 2*(9/t) := mul_le_mul_of_nonneg_left hE (by norm_num)
      _ = _ := by ring
  have he' : ‖exp E‖ ≤ 2 := by
    have h := norm_sub_le (exp E-1) (-1:ℂ)
    have hone : (exp E-1)-(-1)=exp E := by ring
    rw [hone, norm_neg, norm_one] at h
    have hdiv : 18/t ≤ 1 := (div_le_one htp).mpr ht
    linarith
  have hk : ‖k‖ ≤ 1/t := by
    have hke : ‖k‖ = Real.exp (-Real.pi*t) := by
      simp [k, norm_exp, afePoint]
    rw [hke, neg_mul, Real.exp_neg, one_div]
    have hp := Real.pi_gt_three
    have hexp := Real.add_one_le_exp (Real.pi*t)
    apply inv_anti₀ htp
    nlinarith
  have hid : pairChi (afePoint σ t)-afePhase σ t =
      afePhase σ t * ((exp E-1)-exp E*k) := by
    rw [afeChi_phase_factor σ t hσ' (by linarith)]
    dsimp [E,k]; ring
  rw [hid, norm_mul, afePhase_norm]
  have hmul := mul_le_mul he' hk (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have hsub := norm_sub_le (exp E-1) (exp E*k)
  rw [norm_mul] at hsub
  have hlast : ‖(exp E-1)-exp E*k‖ ≤ 20/t := by
    calc
      _ ≤ 18/t+2*(1/t) := hsub.trans (add_le_add he hmul)
      _ = _ := by ring
  calc
    _ ≤ afeHeight t^(1/2-σ)*(20/t) :=
      mul_le_mul_of_nonneg_left hlast (Real.rpow_nonneg (afeHeight_nonneg t) _)
    _ = _ := by ring

theorem afeChi_phase_uniform_positive :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ t →
      ‖pairChi (afePoint σ t)-afePhase σ t‖ ≤ C*afeHeight t^(1/2-σ)/t := by
  obtain ⟨B,hB,hbound⟩ := afeZetaChi_compact_bound (2*Real.pi) 18 (by positivity)
  let C := 20+324*(B+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun σ t hσ hσ' ht => ?_⟩
  have htp : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hq : 1 ≤ afeHeight t := afeHeight_ge_one (by rwa [abs_of_pos htp])
  have hweight := Real.rpow_nonneg (afeHeight_nonneg t) (1/2-σ)
  by_cases hh : 18 ≤ t
  · apply (afeChi_phase_high σ t hσ hσ' hh).trans
    apply div_le_div_of_nonneg_right _ htp.le
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hweight
  have ht18 : t ≤ 18 := le_of_lt (lt_of_not_ge hh)
  have hχ : ‖pairChi (afePoint σ t)‖ ≤ B := by
    have hb := hbound σ t (by linarith) hσ' (by rwa [abs_of_pos htp]) (by rwa [abs_of_pos htp])
    have := norm_nonneg (riemannZeta (afePoint σ t))
    linarith
  have hphase : ‖afePhase σ t‖ ≤ 1 := by
    rw [afePhase_norm]
    exact Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  have hdiff : ‖pairChi (afePoint σ t)-afePhase σ t‖ ≤ B+1 :=
    (norm_sub_le _ _).trans (add_le_add hχ hphase)
  have hq18 : afeHeight t ≤ 18 := by
    unfold afeHeight
    rw [abs_of_pos htp]
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  have hlower : (1/18:ℝ) ≤ afeHeight t^(1/2-σ) := by
    calc
      _ ≤ (afeHeight t)⁻¹ := by
        simpa using inv_anti₀ (lt_of_lt_of_le zero_lt_one hq) hq18
      _ = afeHeight t^(-1:ℝ) := (Real.rpow_neg_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  apply hdiff.trans
  apply (le_div_iff₀ htp).mpr
  have h₁ := mul_le_mul_of_nonneg_left ht18 (by positivity : 0 ≤ B+1)
  have h₂ := mul_le_mul_of_nonneg_left hlower hC.le
  dsimp [C] at h₂ ⊢
  nlinarith

theorem afeChi_phase_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ |t| →
      ‖pairChi (afePoint σ t)-afePhase σ t‖ ≤ C*afeHeight t^(1/2-σ)/|t| := by
  obtain ⟨C,hC,hbound⟩ := afeChi_phase_uniform_positive
  refine ⟨C,hC,fun σ t hσ hσ' ht => ?_⟩
  by_cases ht₀ : 0 ≤ t
  · simpa [abs_of_nonneg ht₀] using hbound σ t hσ hσ' (by rwa [abs_of_nonneg ht₀] at ht)
  · have hn : 0 ≤ -t := by linarith
    have h := hbound σ (-t) hσ hσ' (by simpa [abs_of_neg (lt_of_not_ge ht₀)] using ht)
    rw [afeHeight_neg, afePhase_conj, ← afePoint_conj, afeChi_conj, ← map_sub, norm_conj] at h
    simpa [abs_of_neg (lt_of_not_ge ht₀)] using h

end
end HigherCorrelations
