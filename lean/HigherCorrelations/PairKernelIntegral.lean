import HigherCorrelations.PairKernelAlgebra
import HigherCorrelations.ScalarKernel

/-! UNCONDITIONAL two-kernel integral. Coincident poles are included by dominated
continuity, after evaluating distinct poles on finite intervals. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology

theorem pairKernelProduct_bound (a e f t : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    ‖pairKernelProduct a e f t‖ ≤ 16 / (1+t^2) := by
  have h₁ : ‖scalarKernel (t-a) e‖ ≤ 4 := by
    apply (scalarKernel_bound _ _ he).trans
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (t-a)]
  have h₂ := scalarKernel_bound t f hf
  unfold pairKernelProduct
  rw [norm_mul]
  calc
    _ ≤ 4*(4/(1+t^2)) := mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem pairKernelProduct_integrable (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    Integrable (pairKernelProduct a e f) := by
  have hc : Continuous (pairKernelProduct a e f) :=
    ((scalarKernel_continuous e he).comp (continuous_id.sub continuous_const)).mul
      (scalarKernel_continuous f hf)
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul 16) hc.aestronglyMeasurable
  filter_upwards [] with t
  simpa [div_eq_mul_inv] using pairKernelProduct_bound a e f t he hf

theorem pairKernelCenters_bound (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    ∀ i, |(pairKernelCenters a e f i).im| ≤ 3/4 := by
  intro i
  fin_cases i <;> simpa [pairKernelCenters] using ‹_›

theorem pairKernelIntegral_distinct (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4)
    (ha : a ≠ 0) : pairKernelIntegral a e f = pairKernelValue a e f := by
  let z := pairKernelCenters a e f
  have hz := pairKernelCenters_bound a e f he hf
  have hinj : Function.Injective z := by
    intro i j h
    have hr := congrArg Complex.re h
    clear h
    fin_cases i <;> fin_cases j <;> simp_all [z,pairKernelCenters]
  have hs (i : Fin 2 × Bool) : (pairKernelPole z i).im ≠ 0 := by
    rcases i with ⟨i,s⟩
    cases s
    · exact (pairKernelPole_lower z hz i).ne
    · exact (pairKernelPole_upper z hz i).ne'
  have hp := finite_poles_truncation (pairKernelPole z) (pairKernelPole_injective z hz hinj) hs
  rw [pairKernel_pole_sum z hz hinj] at hp
  have heq (t : ℝ) : (∏ i : Fin 2 × Bool, ((t:ℂ)-pairKernelPole z i))⁻¹ =
      pairKernelProduct a e f t := by
    rw [pairKernelPole_product]
    simp only [pairKernelProduct,scalarKernel,z,pairKernelCenters,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    push_cast
    simp only [mul_inv_rev]
    ring_nf
  simp_rw [heq] at hp
  have hi := intervalIntegral_tendsto_integral (pairKernelProduct_integrable a e f he hf)
    tendsto_neg_atTop_atBot tendsto_id
  have h := tendsto_nhds_unique hi hp
  change pairKernelIntegral a e f = _ at h
  rw [h]
  unfold pairKernelValue z pairKernelCenters
  congr 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring

theorem pairKernelIntegral_eq (a e f : ℝ) (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) :
    pairKernelIntegral a e f = pairKernelValue a e f := by
  have h₁ : Continuous (fun a : ℝ => pairKernelIntegral a e f) := by
    unfold pairKernelIntegral
    apply continuous_of_dominated (F := fun a t => pairKernelProduct a e f t)
      (fun a => (pairKernelProduct_integrable a e f he hf).aestronglyMeasurable)
      (bound := fun t => 16*(1+t^2)⁻¹)
    · intro a
      filter_upwards [] with t
      simpa [div_eq_mul_inv] using pairKernelProduct_bound a e f t he hf
    · exact integrable_inv_one_add_sq.const_mul 16
    · filter_upwards [] with t
      exact ((scalarKernel_continuous e he).comp (continuous_const.sub continuous_id)).mul continuous_const
  have h₂ : Continuous (fun a : ℝ => pairKernelValue a e f) := by
    unfold pairKernelValue
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro a
    convert center_quadratic_ne ((a:ℂ)-Complex.I*e) (-Complex.I*f)
      (by simpa using he) (by simpa using hf) using 1 <;> push_cast <;> ring
  have hd : Dense (Set.univ \ (↑({0} : Finset ℝ) : Set ℝ)) := dense_univ.sdiff_finset ({0} : Finset ℝ)
  have hh := Continuous.ext_on hd h₁ h₂ (fun a ha =>
    pairKernelIntegral_distinct a e f he hf (by simpa using ha.2))
  exact congrFun hh a

theorem pairKernelIntegral_coincident (e : ℝ) (he : |e| ≤ 3/4) :
    pairKernelIntegral 0 e e = (Real.pi : ℂ)/2 := by
  rw [pairKernelIntegral_eq 0 e e he he]
  unfold pairKernelValue
  push_cast
  ring

end
end HigherCorrelations
