import HigherCorrelations.SineSchwartzLines

/-! UNCONDITIONAL continuous L1 marginals of plane Schwartz tests. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

theorem sineMarginal_majorant (F : 𝓢(ℝ × ℝ,ℂ)) :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ y z, ‖F (y,z)‖ ≤ B z := by
  let C := 4*(Finset.Iic (2,0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨fun z => C*(1+‖z‖)^(-(2:ℝ)), ?_, ?_⟩
  · exact (integrable_one_add_norm (by norm_num : (Module.finrank ℝ ℝ:ℝ) < 2)).const_mul C
  · intro y z
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl F (y,z)
    have hz : ‖z‖ ≤ ‖(y,z)‖ := by simp [Prod.norm_def]
    have hb : (1+‖z‖)^2*‖F (y,z)‖ ≤ C := by
      calc
        _ ≤ (1+‖(y,z)‖)^2*‖F (y,z)‖ := by gcongr
        _ ≤ C := by simpa [C,show (2:ℝ)^2 = 4 by norm_num] using h
    change ‖F (y,z)‖ ≤ C*(1+‖z‖)^(-(2:ℝ))
    rw [Real.rpow_neg (by positivity),Real.rpow_two,← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hb)

theorem sineMarginal_continuous (F : 𝓢(ℝ × ℝ,ℂ)) : Continuous (sineMarginal F) := by
  obtain ⟨B,hB,hbound⟩ := sineMarginal_majorant F
  exact continuous_of_dominated (fun y => (F.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (fun y => Filter.Eventually.of_forall (hbound y)) hB
    (Filter.Eventually.of_forall fun z => F.continuous.comp (by fun_prop))

theorem sineMarginal_integrable (F : 𝓢(ℝ × ℝ,ℂ)) : Integrable (sineMarginal F) := by
  have h : Integrable (fun p : ℝ × ℝ => F (p.1,p.2)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact F.integrable
  exact h.integral_prod_left

theorem sineMarginal_fourier (F : 𝓢(ℝ × ℝ,ℂ)) (r : ℝ) :
    pairMeanFourier (sineMarginal F) r =
      ∫ p : ℝ × ℝ, pairMeanCharacter (-p.1*r)*F p := by
  have hi : Integrable (fun p : ℝ × ℝ => pairMeanCharacter (-p.1*r)*F p) := by
    apply F.integrable.norm.mono' ((pairMeanCharacter_continuous.comp (by fun_prop)).mul F.continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by simp [norm_mul,pairMeanCharacter_norm]
  rw [pairMeanFourier,Measure.volume_eq_prod,integral_prod _ (by simpa only [← Measure.volume_eq_prod] using hi)]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (integral_const_mul _ _).symm

end
end HigherCorrelations
