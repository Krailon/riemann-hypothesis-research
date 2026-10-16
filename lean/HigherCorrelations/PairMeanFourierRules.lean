import HigherCorrelations.PairMeanFourier

/-! UNCONDITIONAL Fourier scaling, translation, and conjugation rules in
the project's explicit cycles convention. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex

theorem pairMeanFourier_zero (f : ℝ → ℂ) : pairMeanFourier f 0 = ∫ t, f t := by
  simp [pairMeanFourier, pairMeanCharacter]

theorem pairMeanFourier_const_mul (f : ℝ → ℂ) (a : ℂ) (ξ : ℝ) :
    pairMeanFourier (fun t => a*f t) ξ = a*pairMeanFourier f ξ := by
  simp only [pairMeanFourier, ← integral_const_mul]
  congr 1
  funext t
  ring

theorem pairMeanFourier_add (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (ξ : ℝ) : pairMeanFourier (fun t => f t+g t) ξ =
      pairMeanFourier f ξ+pairMeanFourier g ξ := by
  unfold pairMeanFourier
  simp_rw [mul_add]
  apply integral_add
  · apply hf.norm.mono' ((pairMeanCharacter_continuous.comp (by fun_prop)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    filter_upwards [] with t
    simp [pairMeanCharacter_norm]
  · apply hg.norm.mono' ((pairMeanCharacter_continuous.comp (by fun_prop)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards [] with t
    simp [pairMeanCharacter_norm]

theorem pairMeanFourier_div (f : ℝ → ℂ) (a ξ : ℝ) (ha : a ≠ 0) :
    pairMeanFourier (fun t => f (t/a)) ξ = ((|a|:ℝ):ℂ)*pairMeanFourier f (a*ξ) := by
  unfold pairMeanFourier
  have he : (fun t : ℝ => pairMeanCharacter (-t*ξ)*f (t/a)) =
      fun t : ℝ => (fun u : ℝ => pairMeanCharacter (-u*(a*ξ))*f u) (t/a) := by
    funext t
    congr 2
    field_simp
    <;> ring
  rw [he]
  exact (Measure.integral_comp_div (fun u : ℝ => pairMeanCharacter (-u*(a*ξ))*f u) a).trans
    (by rw [Complex.real_smul])

theorem pairMeanFourier_mul (f : ℝ → ℂ) (a ξ : ℝ) (ha : a ≠ 0) :
    pairMeanFourier (fun t => f (a*t)) ξ = ((|a|⁻¹:ℝ):ℂ)*pairMeanFourier f (ξ/a) := by
  have h := pairMeanFourier_div f a⁻¹ ξ (inv_ne_zero ha)
  simpa only [div_inv_eq_mul, mul_comm, abs_inv, ofReal_inv, div_eq_mul_inv, inv_inv] using h

theorem pairMeanFourier_sub (f : ℝ → ℂ) (a ξ : ℝ) :
    pairMeanFourier (fun t => f (t-a)) ξ = pairMeanCharacter (-a*ξ)*pairMeanFourier f ξ := by
  unfold pairMeanFourier
  rw [← integral_const_mul]
  have he : (fun t : ℝ => pairMeanCharacter (-t*ξ)*f (t-a)) =
      fun t : ℝ => (fun u : ℝ => pairMeanCharacter (-a*ξ)*(pairMeanCharacter (-u*ξ)*f u)) (t-a) := by
    funext t
    dsimp only
    rw [← mul_assoc, ← pairMeanCharacter_add]
    congr 2
    ring
  rw [he]
  exact integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => pairMeanCharacter (-a*ξ)*(pairMeanCharacter (-u*ξ)*f u)) a

end
end HigherCorrelations
