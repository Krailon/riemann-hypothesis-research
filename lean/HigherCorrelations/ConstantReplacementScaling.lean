import HigherCorrelations.ConstantReplacementDefinitions
import HigherCorrelations.ConstantKernelBounds
import HigherCorrelations.UniformHeightApplications

/-! UNCONDITIONAL conversion to the exact project scales, including endpoints. -/
namespace HigherCorrelations
noncomputable section

theorem replacementRadius_nonneg (T : ℝ) (v : ReplacementTriple) :
    0 ≤ replacementRadius T v := (abs_nonneg _).trans (le_max_left _ _)

theorem replacementHorizontal_bounds (T : ℝ) (hq : 0 ≤ Real.log T) (v : ReplacementTriple) :
    0 ≤ replacementHorizontal T v ∧ replacementHorizontal T v ≤ Real.log T/2 ∧
    ∀ j, Real.log T*|replacementDelta v j| ≤ replacementHorizontal T v := by
  have hd (j) : |replacementDelta v j| ≤ 1/2 := (occurrence_displacement_lt (v j)).le
  refine ⟨mul_nonneg hq ((abs_nonneg _).trans (le_max_left _ _)), ?_, ?_⟩
  · unfold replacementHorizontal
    have hm : max |replacementDelta v 0| (max |replacementDelta v 1| |replacementDelta v 2|) ≤ 1/2 :=
      max_le (hd 0) (max_le (hd 1) (hd 2))
    nlinarith [mul_le_mul_of_nonneg_left hm hq]
  · intro j
    unfold replacementHorizontal
    apply mul_le_mul_of_nonneg_left _ hq
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

theorem constantKernelEmpty_scaled (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) (q ℓ r x : ℝ)
    (hq : 0 < q) (hℓ : 0 < ℓ) (hr : 0≤r) (hx : 0≤x)
    (hscale : q ≤ 4*Real.pi*ℓ) (ha : |ℓ*a|≤r) (hd : |ℓ*d|≤r)
    (hh : ∀ j, q*|δ j|≤x) :
    ‖constantKernelEmpty a d δ-kernelBenchmark‖ ≤
      replacementScaleConstant*(r^2+x^2)/q^2 := by
  have hg (z : ℝ) (hz : |ℓ*z|≤r) : q^2*z^2 ≤ 16*Real.pi^2*r^2 := by
    have h1 : q*|z| ≤ 4*Real.pi*r := by
      rw [abs_mul, abs_of_pos hℓ] at hz
      nlinarith [mul_le_mul_of_nonneg_right hscale (abs_nonneg z), Real.pi_pos]
    have h2 := mul_self_le_mul_self (by positivity : 0≤q*|z|) h1
    nlinarith [sq_abs z]
  have hh2 (j) : q^2*δ j^2 ≤ x^2 := by
    have h := mul_self_le_mul_self (by positivity : 0≤q*|δ j|) (hh j)
    nlinarith [sq_abs (δ j)]
  have he : q^2*constantKernelEnergy a d δ ≤ (32*Real.pi^2+3)*(r^2+x^2) := by
    simp only [constantKernelEnergy, Fin.sum_univ_three]
    nlinarith [hg a ha, hg d hd, hh2 0, hh2 1, hh2 2,
      mul_nonneg (sq_nonneg Real.pi) (sq_nonneg x), sq_nonneg r]
  have hb := constantKernelEmpty_pointwise a d δ hδ
  have hb' : ‖constantKernelEmpty a d δ-kernelBenchmark‖ ≤ constantKernelBound*constantKernelEnergy a d δ :=
    hb.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by unfold constantKernelBound; positivity))
  apply (le_div_iff₀ (sq_pos_of_pos hq)).mpr
  unfold replacementScaleConstant
  have hp := mul_le_mul_of_nonneg_left he (show 0≤4096*Real.pi by positivity)
  have hn := mul_le_mul_of_nonneg_right hb' (sq_nonneg q)
  unfold constantKernelBound at hn
  nlinarith

theorem replacementKernel_scaled (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (v : ReplacementTriple) :
    ‖replacementKernel v-kernelBenchmark‖ ≤ replacementScaleConstant*
      ((replacementRadius T v)^2+(replacementHorizontal T v)^2)/(Real.log T)^2 := by
  have ht := uniformHeightThreshold_bounds hT
  have hx := replacementHorizontal_bounds T (by linarith [ht.2.1]) v
  apply constantKernelEmpty_scaled _ _ _ (fun j => (occurrence_displacement_lt (v j)).le)
    _ _ _ _ (by linarith [ht.2.1]) (by linarith [ht.2.2]) (replacementRadius_nonneg T v) hx.1
    (meanSpacing_log_comparison hT) (le_max_left _ _) (le_max_right _ _) hx.2.2

end
end HigherCorrelations
