import HigherCorrelations.PairedMellinTransform
import HigherCorrelations.PairedMellinBounds

/-! UNCONDITIONAL paired Mellin kernel, with absolute convergence and exact endpoint. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem pairedMellin_inverse_bridge (y : ℝ) (hy : 0<y) :
    pairedMellinKernel y = mellinInv 2 pairedMellinSymbol y⁻¹ := by
  unfold pairedMellinKernel mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have he : ((y⁻¹ : ℝ):ℂ)^(-(2+(t:ℂ)*Complex.I)) =
      Complex.exp ((2+(t:ℂ)*Complex.I)*(Real.log y:ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast inv_ne_zero hy.ne')]
    rw [← Complex.ofReal_log (inv_pos.mpr hy).le, Real.log_inv]
    congr 1
    push_cast
    ring
  norm_num only [Complex.ofReal_ofNat]
  rw [he]
  simp only [pairedMellinIntegrand, pairedMellinSymbol, smul_eq_mul]
  ring

theorem pairedMellin_inversion (y : ℝ) (hy : 0<y) :
    pairedMellinKernel y = pairedMellinSeed y⁻¹ := by
  have ht := pairedMellinSeed_transform 2 (by norm_num)
  have hv : Complex.VerticalIntegrable (mellin pairedMellinSeed) 2 := by
    apply pairedMellinSymbol_vertical.congr
    filter_upwards [] with t
    exact (pairedMellinSeed_transform (2+(t:ℂ)*Complex.I) (by simp)).2.symm
  rw [pairedMellin_inverse_bridge y hy]
  have he : mellinInv 2 pairedMellinSymbol y⁻¹ = mellinInv 2 (mellin pairedMellinSeed) y⁻¹ := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    norm_num only [Complex.ofReal_ofNat]
    rw [(pairedMellinSeed_transform (2+(t:ℂ)*Complex.I) (by simp)).2]
  rw [he]
  exact mellinInv_mellin_eq 2 pairedMellinSeed (inv_pos.mpr hy) ht.1 hv
    (pairedMellinSeed_continuous _ (inv_pos.mpr hy))

theorem pairedMellinKernel_gt_one (y : ℝ) (hy : 1<y) :
    pairedMellinKernel y = (y : ℂ) - (y : ℂ)⁻¹ := by
  rw [pairedMellin_inversion y (by linarith)]
  have hp : 0<y⁻¹ := inv_pos.mpr (by linarith)
  have hq : y⁻¹≤1 := (inv_le_one₀ (by linarith)).mpr hy.le
  simp [pairedMellinSeed, hp, hq]

theorem pairedMellinKernel_le_one (y : ℝ) (hy : 0<y) (hy1 : y≤1) :
    pairedMellinKernel y = 0 := by
  rw [pairedMellin_inversion y hy]
  by_cases h : y=1
  · subst y; simp [pairedMellinSeed]
  · have hh : 1<y⁻¹ := (one_lt_inv₀ hy).mpr (lt_of_le_of_ne hy1 h)
    simp [pairedMellinSeed, show ¬ y⁻¹≤1 by linarith]

theorem pairedMellinKernel_at_one : pairedMellinKernel 1 = 0 :=
  pairedMellinKernel_le_one 1 (by norm_num) le_rfl

theorem pairedMellin_kernel (y : ℝ) (hy : 0<y) :
    Integrable (pairedMellinIntegrand y) ∧
    pairedMellinUpwardIntegral y = if 1<y then (y:ℂ)-(y:ℂ)⁻¹ else 0 := by
  refine ⟨pairedMellinIntegrand_integrable y hy, ?_⟩
  rw [pairedMellin_upward_normalization]
  split_ifs with h
  · exact pairedMellinKernel_gt_one y h
  · exact pairedMellinKernel_le_one y hy (le_of_not_gt h)

end
end HigherCorrelations
