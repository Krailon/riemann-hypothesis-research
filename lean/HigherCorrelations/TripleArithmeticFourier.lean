import HigherCorrelations.TripleConvolutionMass
import HigherCorrelations.TripleLogFourierIdentity

/-! UNCONDITIONAL identification of prime series with integer-frequency series.
The absent integers 0 and 1 have exactly zero coefficients. -/
namespace HigherCorrelations
noncomputable section

theorem tripleNat_tsum_ge_two {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : ℕ → E) (h0 : f 0=0) (h1 : f 1=0) :
    (∑' n : LogGapIndex, f n.val) = ∑' n : ℕ, f n := by
  apply tsum_subtype_eq_of_support_subset
  intro n hn
  by_contra h
  have he : n=0 ∨ n=1 := by change ¬2≤n at h; omega
  rcases he with rfl | rfl
  · exact hn h0
  · exact hn h1

theorem tripleArithmetic_phase_summable (x t : ℝ) (hx : 1≤x) :
    Summable (fun n : ℕ => ‖(tripleArithmeticCoefficient x n:ℂ)*
      pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)‖) := by
  simpa only [norm_mul,pairMeanCharacter_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (tripleArithmeticCoefficient_nonneg x hx _)] using tripleArithmeticCoefficient_summable x hx

theorem tripleArithmetic_phase_sum (x t : ℝ) (hx : 1≤x) :
    (∑' n : ℕ, (tripleArithmeticCoefficient x n:ℂ)*pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)) =
      pairPrimeSeries (x,t) := by
  rw [(tripleArithmetic_phase_summable x t hx).of_norm.tsum_eq_zero_add]
  simp only [tripleArithmeticCoefficient_zero,Complex.ofReal_zero,zero_mul,zero_add]
  apply tsum_congr
  intro n
  rw [tripleArithmeticCoefficient_succ,pairMeanPrimeTerm_frequency]
  simp only [pairMeanPrimeFrequency,Nat.cast_add,Nat.cast_one]

theorem tripleLogCoefficient_series (x t : ℝ) (hx : 1≤x) :
    pairFrequencySum tripleLogFrequency (tripleLogCoefficient x) t = pairPrimeSeries (x,t) := by
  change (∑' n : LogGapIndex, (tripleArithmeticCoefficient x n.val:ℂ)*
    pairMeanCharacter ((-Real.log n.val/(2*Real.pi))*t)) = _
  rw [tripleNat_tsum_ge_two (fun n => (tripleArithmeticCoefficient x n:ℂ)*pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)) (by simp [tripleArithmeticCoefficient_zero])
    (by simp [tripleArithmeticCoefficient_one]),tripleArithmetic_phase_sum x t hx]

theorem tripleArithmetic_phase_mul (X Y t : ℝ) (m n : ℕ) :
    ((tripleArithmeticCoefficient X m:ℂ)*pairMeanCharacter ((-Real.log m/(2*Real.pi))*t))*
      ((tripleArithmeticCoefficient Y n:ℂ)*pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)) =
    ((tripleArithmeticCoefficient X m*tripleArithmeticCoefficient Y n:ℝ):ℂ)*
      pairMeanCharacter ((-Real.log (m*n)/(2*Real.pi))*t) := by
  by_cases hm : m=0
  · simp [hm,tripleArithmeticCoefficient_zero]
  by_cases hn : n=0
  · simp [hn,tripleArithmeticCoefficient_zero]
  rw [Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
  have he : -Real.log (m:ℝ)/(2*Real.pi)*t + -Real.log (n:ℝ)/(2*Real.pi)*t =
      -(Real.log m+Real.log n)/(2*Real.pi)*t := by ring
  rw [← he,pairMeanCharacter_add]
  push_cast
  ring

theorem tripleArithmeticConvolution_phase_fiber (X Y t : ℝ) (r : ℕ) :
    (∑' p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r},
      ((tripleArithmeticCoefficient X p.val.1:ℂ)*pairMeanCharacter ((-Real.log p.val.1/(2*Real.pi))*t))*
        ((tripleArithmeticCoefficient Y p.val.2:ℂ)*pairMeanCharacter ((-Real.log p.val.2/(2*Real.pi))*t))) =
    (tripleArithmeticConvolution X Y r:ℂ)*pairMeanCharacter ((-Real.log r/(2*Real.pi))*t) := by
  have he (p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r}) :
      ((tripleArithmeticCoefficient X p.val.1:ℂ)*pairMeanCharacter ((-Real.log p.val.1/(2*Real.pi))*t))*
        ((tripleArithmeticCoefficient Y p.val.2:ℂ)*pairMeanCharacter ((-Real.log p.val.2/(2*Real.pi))*t)) =
      ((tripleArithmeticCoefficient X p.val.1*tripleArithmeticCoefficient Y p.val.2:ℝ):ℂ)*
        pairMeanCharacter ((-Real.log r/(2*Real.pi))*t) := by
    rw [tripleArithmetic_phase_mul,← Nat.cast_mul]
    rw [show p.val.1*p.val.2=r from p.property]
  simp_rw [he]
  rw [tsum_mul_right,← Complex.ofReal_tsum,tripleArithmeticConvolution_fiber]

theorem tripleArithmeticConvolution_phase_sum (X Y t : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' r : ℕ, (tripleArithmeticConvolution X Y r:ℂ)*pairMeanCharacter ((-Real.log r/(2*Real.pi))*t)) =
      pairPrimeSeries (X,t)*pairPrimeSeries (Y,t) := by
  have hx := tripleArithmetic_phase_summable X t hX
  have hy := tripleArithmetic_phase_summable Y t hY
  have hp := tsum_mul_tsum_of_summable_norm hx hy
  have hnorm : Summable (fun p : ℕ × ℕ =>
      ‖((tripleArithmeticCoefficient X p.1:ℂ)*pairMeanCharacter ((-Real.log p.1/(2*Real.pi))*t))*
        ((tripleArithmeticCoefficient Y p.2:ℂ)*pairMeanCharacter ((-Real.log p.2/(2*Real.pi))*t))‖) := by
    simpa only [norm_mul] using hx.mul_of_nonneg hy (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hh := hnorm.of_norm.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1*p.2)
  simp only [tripleArithmeticConvolution_phase_fiber] at hh
  rw [← hp,tripleArithmetic_phase_sum X t hX,tripleArithmetic_phase_sum Y t hY] at hh
  exact hh.tsum_eq

theorem tripleLogConvolution_series (X Y t : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    pairFrequencySum tripleLogFrequency (tripleLogConvolution X Y) t =
      pairPrimeSeries (X,t)*pairPrimeSeries (Y,t) := by
  change (∑' n : LogGapIndex, (tripleArithmeticConvolution X Y n.val:ℂ)*
    pairMeanCharacter ((-Real.log n.val/(2*Real.pi))*t)) = _
  rw [tripleNat_tsum_ge_two (fun n => (tripleArithmeticConvolution X Y n:ℂ)*pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)) (by simp [tripleArithmeticConvolution])
    (by simp [tripleArithmeticConvolution,tripleArithmeticCoefficient_one]),
    tripleArithmeticConvolution_phase_sum X Y t hX hY]

end
end HigherCorrelations
