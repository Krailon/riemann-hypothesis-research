import HigherCorrelations.TripleConvolutionBounds

/-! UNCONDITIONAL regrouping by the integer product, preserving all ordered factors. -/
namespace HigherCorrelations
noncomputable section
open Set

theorem tripleArithmeticConvolution_fiber (X Y : ℝ) (r : ℕ) :
    tripleArithmeticConvolution X Y r =
      ∑' p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r},
        tripleArithmeticCoefficient X p.val.1*tripleArithmeticCoefficient Y p.val.2 := by
  by_cases hr : r=0
  · subst r
    have hz : ∀ p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {(0:ℕ)},
        tripleArithmeticCoefficient X p.val.1*tripleArithmeticCoefficient Y p.val.2=0 := by
      intro p
      have hp : p.val.1*p.val.2=0 := p.property
      rcases Nat.mul_eq_zero.mp hp with h | h <;> simp [h,tripleArithmeticCoefficient_zero]
    simp [tripleArithmeticConvolution,hz]
  · have he : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r} = (r.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
      ext p
      simp [Nat.mem_divisorsAntidiagonal,hr]
    rw [he,Finset.tsum_subtype' r.divisorsAntidiagonal
      (fun p => tripleArithmeticCoefficient X p.1*tripleArithmeticCoefficient Y p.2),Nat.sum_divisorsAntidiagonal (fun a b => tripleArithmeticCoefficient X a*tripleArithmeticCoefficient Y b)]
    rfl

theorem tripleArithmeticCoefficient_mass (x : ℝ) (hx : 1≤x) :
    (∑' n, tripleArithmeticCoefficient x n) = triplePrimeMass x := by
  rw [(tripleArithmeticCoefficient_summable x hx).tsum_eq_zero_add,tripleArithmeticCoefficient_zero,zero_add]
  simp only [tripleArithmeticCoefficient_succ,triplePrimeMass]

theorem tripleArithmeticConvolution_hasSum (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    HasSum (tripleArithmeticConvolution X Y) (triplePrimeMass X*triplePrimeMass Y) := by
  have hx := tripleArithmeticCoefficient_summable X hX
  have hy := tripleArithmeticCoefficient_summable Y hY
  have hp : Summable (fun p : ℕ × ℕ => tripleArithmeticCoefficient X p.1*tripleArithmeticCoefficient Y p.2) :=
    hx.mul_of_nonneg hy (tripleArithmeticCoefficient_nonneg X hX) (tripleArithmeticCoefficient_nonneg Y hY)
  have h := (hx.hasSum.mul hy.hasSum hp).tsum_fiberwise (fun p : ℕ × ℕ => p.1*p.2)
  simp only [← tripleArithmeticConvolution_fiber,tripleArithmeticCoefficient_mass X hX,
    tripleArithmeticCoefficient_mass Y hY] at h
  exact h

theorem tripleArithmeticConvolution_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (tripleArithmeticConvolution X Y) :=
  (tripleArithmeticConvolution_hasSum X Y hX hY).summable

theorem tripleArithmeticConvolution_mass (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' r, tripleArithmeticConvolution X Y r) = triplePrimeMass X*triplePrimeMass Y :=
  (tripleArithmeticConvolution_hasSum X Y hX hY).tsum_eq

theorem tripleLogConvolution_mass_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun n => ‖tripleLogConvolution X Y n‖) := by
  have h := (tripleArithmeticConvolution_summable X Y hX hY).comp_injective
    (show Function.Injective (fun n : LogGapIndex => n.val) from Subtype.val_injective)
  simpa only [Function.comp_def,tripleLogConvolution,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tripleArithmeticConvolution_nonneg X Y hX hY _)] using h

theorem tripleLogConvolution_mass_bound (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    tripleLogMass (tripleLogConvolution X Y) ≤ triplePrimeMass X*triplePrimeMass Y := by
  have h := Summable.tsum_subtype_le (tripleArithmeticConvolution X Y) {n : ℕ | 2≤n}
    (tripleArithmeticConvolution_nonneg X Y hX hY) (tripleArithmeticConvolution_summable X Y hX hY)
  simp only [tripleLogMass,tripleLogConvolution,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tripleArithmeticConvolution_nonneg X Y hX hY _),
    tripleArithmeticConvolution_mass X Y hX hY]
  rw [tripleArithmeticConvolution_mass X Y hX hY] at h
  convert h using 1 <;> rfl

end
end HigherCorrelations
