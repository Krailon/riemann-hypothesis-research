import Mathlib.Analysis.MeanInequalities

/-! UNCONDITIONAL finite weighted Cauchy--Schwarz with row and column bounds. -/
namespace HigherCorrelations
noncomputable section

theorem tripleFiniteSchur {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (K : ι → κ → ℝ) (u : ι → ℝ) (v : κ → ℝ) (A : ι → ℝ) (B : κ → ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ t, 0≤K i j)
    (hA : ∀ i ∈ s, ∑ j ∈ t, K i j ≤ A i)
    (hB : ∀ j ∈ t, ∑ i ∈ s, K i j ≤ B j) :
    (∑ i ∈ s, ∑ j ∈ t, K i j*u i*v j) ≤
      Real.sqrt ((∑ i ∈ s, A i*u i^2)*(∑ j ∈ t, B j*v j^2)) := by
  have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s.product t)
    (r := fun p => K p.1 p.2*u p.1*v p.2)
    (f := fun p => K p.1 p.2*u p.1^2)
    (g := fun p => K p.1 p.2*v p.2^2)
    (fun p hp => mul_nonneg (hK p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    (fun p hp => mul_nonneg (hK p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    (fun _ _ => by nlinarith [sq_nonneg (0:ℝ)])
  simp only [Finset.product_eq_sprod,Finset.sum_product] at hsq
  have hf : (∑ i ∈ s, ∑ j ∈ t, K i j*u i^2) ≤ ∑ i ∈ s, A i*u i^2 := by
    apply Finset.sum_le_sum
    intro i hi
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hA i hi) (sq_nonneg _)
  have hg : (∑ i ∈ s, ∑ j ∈ t, K i j*v j^2) ≤ ∑ j ∈ t, B j*v j^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hB j hj) (sq_nonneg _)
  have hf0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ t, K i j*u i^2 :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (hK i hi j hj) (sq_nonneg _)))
  have hg0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ t, K i j*v j^2 :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (hK i hi j hj) (sq_nonneg _)))
  have hb := hsq.trans (mul_le_mul hf hg hg0 (hf0.trans hf))
  have he := Real.sq_sqrt (mul_nonneg (hf0.trans hf) (hg0.trans hg))
  have hp := Real.sqrt_nonneg ((∑ i ∈ s, A i*u i^2)*(∑ j ∈ t, B j*v j^2))
  nlinarith

end
end HigherCorrelations
