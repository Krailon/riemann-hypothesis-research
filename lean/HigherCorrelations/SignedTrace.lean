import HigherCorrelations.SignedTestAssembly
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! UNCONDITIONAL signed traces, parameterized by dr (not arclength). -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem signed_trace_integrable (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (v : ℝ × ℝ) (hv : v ≠ 0) (w : ℝ → ℂ) (hw : Continuous w) :
    Integrable (fun r : ℝ => w r*φ (r • v)) := by
  have hs := hc.comp_isClosedEmbedding (isClosedEmbedding_smul_left (𝕜 := ℝ) hv)
  exact (hw.mul (hφ.comp (by fun_prop))).integrable_of_hasCompactSupport hs.mul_left

theorem signed_trace_split (f : ℝ → ℂ) (hf : Integrable (fun r => ((|r|:ℝ):ℂ)*f r)) :
    (∫ r : ℝ, ((|r|:ℝ):ℂ)*f r) = ∫ r : ℝ in Ioi 0, (r:ℂ)*(f r+f (-r)) := by
  have he := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hf
  simp only [compl_Ioi] at he
  have hn := integral_comp_neg_Ioi 0 (fun r => ((|r|:ℝ):ℂ)*f r)
  simp only [neg_zero] at hn
  rw [← he,← hn]
  have hi := hf.integrableOn (s := Ioi (0:ℝ))
  have hj : IntegrableOn (fun r : ℝ => ((|-r|:ℝ):ℂ)*f (-r)) (Ioi 0) :=
    hf.comp_neg.integrableOn
  rw [← integral_add hi hj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [abs_neg,abs_of_pos (show 0<r from hr)]
  ring

theorem signed_sector_limit (φ : ℝ × ℝ → ℂ) (j : Fin 6) :
    signedConjugate j (tripleQuadrantLimit (signedPullback φ j)) =
      φ (0,0)/4 + (3/4:ℂ)*∫ r : ℝ in Ioi 0,
        (r:ℂ)*(φ (signedSector j (r,0))+φ (signedSector j (0,r))) := by
  have hz : signedSector j (0,0)=(0,0) := by fin_cases j <;> norm_num [signedSector]
  unfold tripleQuadrantLimit signedPullback signedConjugate
  split_ifs
  · rw [hz]
  · simp only [Complex.star_def,map_add,map_div₀,map_mul,map_ofNat,
      ← integral_conj,hz,Complex.conj_conj]
    congr 1
    apply congrArg ((3/4:ℂ)*·)
    apply integral_congr_ae
    filter_upwards [] with r
    simp

theorem signed_limit_sector_sum (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∑ j : Fin 6, signedConjugate j (tripleQuadrantLimit (signedPullback φ j))) = signedLimit φ := by
  have hzero : ((1,0):ℝ × ℝ) ≠ 0 := by norm_num
  have hone : ((0,1):ℝ × ℝ) ≠ 0 := by norm_num
  have hdiag : ((1,-1):ℝ × ℝ) ≠ 0 := by norm_num
  have h0 := signed_trace_integrable φ hφ hc (1,0) hzero (fun r => ((|r|:ℝ):ℂ)) (by fun_prop)
  have h1 := signed_trace_integrable φ hφ hc (0,1) hone (fun r => ((|r|:ℝ):ℂ)) (by fun_prop)
  have h2 := signed_trace_integrable φ hφ hc (1,-1) hdiag (fun r => ((|r|:ℝ):ℂ)) (by fun_prop)
  have ht : Integrable (fun r : ℝ => ((|r|:ℝ):ℂ)*(φ (r,0)+φ (0,r)+φ (r,-r))) := by
    convert (h0.add h1).add h2 using 1
    ext r
    simp [smul_eq_mul,mul_add]
  have hj (j : Fin 6) : IntegrableOn (fun r : ℝ =>
      (r:ℂ)*(φ (signedSector j (r,0))+φ (signedSector j (0,r)))) (Ioi 0) := by
    have hs := hc.comp_homeomorph (signedSectorEquiv j).toHomeomorph
    have hh := hφ.comp (signedSectorEquiv j).continuous
    have ha := signed_trace_integrable _ hh hs (1,0) hzero (fun r => (r:ℂ)) (by fun_prop)
    have hb := signed_trace_integrable _ hh hs (0,1) hone (fun r => (r:ℂ)) (by fun_prop)
    convert (ha.add hb).integrableOn using 1
    ext r
    simp [Function.comp_def,smul_eq_mul,mul_add,signedSectorEquiv_apply]
  simp_rw [signed_sector_limit]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← integral_finset_sum _ (fun j _ => hj j)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [signedLimit,signed_trace_split _ ht]
  have he : (fun r : ℝ => ∑ j : Fin 6,
      (r:ℂ)*(φ (signedSector j (r,0))+φ (signedSector j (0,r)))) =
      fun r : ℝ => 2*((r:ℂ)*(φ (r,0)+φ (0,r)+φ (r,-r)+(φ (-r,0)+φ (0,-r)+φ (-r,r)))) := by
    funext r
    simp [Fin.sum_univ_succ,signedSector]
    ring
  rw [he,integral_const_mul]
  simp only [neg_neg]
  ring

end
end HigherCorrelations
