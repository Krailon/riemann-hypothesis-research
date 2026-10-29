import HigherCorrelations.TripleQuadrantGeometry

/-! UNCONDITIONAL scale conversion at axes and origin. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_product_height (κ T : ℝ) (hκ : 0≤κ)
    (hT : 2*Real.pi<T) (p : ℝ × ℝ) (hp : p ∈ tripleQuadrantMargin κ) :
    (tripleTestBase T)^p.1*(tripleTestBase T)^p.2≤T ∧
    ((tripleTestBase T)^p.1*(tripleTestBase T)^p.2)/T≤(tripleTestBase T)^(-κ) := by
  have ht := tripleTestBase_bounds T hT
  have hb : 0<tripleTestBase T := by linarith [ht.2.1]
  have hT0 : 0<T := by linarith [ht.1]
  have hz := (tripleQuadrant_scale_range κ T p hT hp).2.2
  constructor
  · apply hz.trans
    apply le_trans (Real.rpow_le_rpow_of_exponent_le ht.2.1.le (show 1-κ≤(1:ℝ) by linarith))
    simpa using ht.2.2
  · apply (div_le_iff₀ hT0).mpr
    calc
      _ ≤ (tripleTestBase T)^(1-κ) := hz
      _ = (tripleTestBase T)*(tripleTestBase T)^(-κ) := by rw [sub_eq_add_neg,Real.rpow_add hb,Real.rpow_one]
      _ ≤ T*(tripleTestBase T)^(-κ) := mul_le_mul_of_nonneg_right ht.2.2 (Real.rpow_nonneg hb.le _)
      _ = _ := by ring

theorem tripleBoundary_inverse_scale (B x : ℝ) (hB : 0<B) :
    1/B^x=Real.exp (-(Real.log B*x)) := by
  rw [Real.rpow_def_of_pos hB,Real.exp_neg,one_div]

theorem tripleBoundary_inverse_product_square (B x y : ℝ) (hB : 0<B) :
    1/(B^x*B^y)^2 =
      Real.exp (-((2*Real.log B)*x))*Real.exp (-((2*Real.log B)*y)) := by
  rw [Real.rpow_def_of_pos hB,Real.rpow_def_of_pos hB,mul_pow]
  rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  simp only [one_div,mul_inv,← Real.exp_neg]
  congr 2 <;> congr 1 <;> ring

end
end HigherCorrelations
