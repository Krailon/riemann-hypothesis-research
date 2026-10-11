import HigherCorrelations.RationalTransferDefinitions
import HigherCorrelations.ActualCorrelationConvergence

/-! UNCONDITIONAL global bounds on the closed horizontal parameter cube. -/
namespace HigherCorrelations
noncomputable section

theorem rational_denominator_lower (z : ℂ) (hz : |z.im| ≤ 1) :
    3 + z.re ^ 2 ≤ ‖4 + z ^ 2‖ := by
  have h := Complex.re_le_norm (4 + z ^ 2)
  have hi : z.im ^ 2 ≤ 1 := by nlinarith [abs_le.mp hz |>.1, abs_le.mp hz |>.2]
  have hr : (4 + z ^ 2).re = 4 + z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]; ring
  rw [hr] at h
  linarith

theorem rational_denominator_ne_zero (z : ℂ) (hz : |z.im| ≤ 1) :
    4 + z ^ 2 ≠ 0 := by
  intro h
  have hb := rational_denominator_lower z hz
  rw [h, norm_zero] at hb
  nlinarith [sq_nonneg z.re]

theorem rationalKernel_reciprocal (z₁ z₂ z₃ : ℂ)
    (h₁₂ : 4 + (z₁-z₂)^2 ≠ 0) (h₁₃ : 4 + (z₁-z₃)^2 ≠ 0)
    (h₂₃ : 4 + (z₂-z₃)^2 ≠ 0) :
    rationalKernel z₁ z₂ z₃ = (Real.pi : ℂ) *
      (1 / ((4+(z₁-z₂)^2)*(4+(z₁-z₃)^2)) +
       1 / ((4+(z₁-z₂)^2)*(4+(z₂-z₃)^2)) +
       1 / ((4+(z₁-z₃)^2)*(4+(z₂-z₃)^2)) +
       12 / ((4+(z₁-z₂)^2)*(4+(z₁-z₃)^2)*(4+(z₂-z₃)^2))) := by
  unfold rationalKernel
  field_simp [h₁₂, h₁₃, h₂₃]
  ring

private theorem reciprocal_pair_bound (A B : ℂ) (hA : 3 ≤ ‖A‖) (hB : 3 ≤ ‖B‖) :
    ‖1 / (A * B)‖ ≤ (1 : ℝ) / 9 := by
  rw [norm_div, norm_one, norm_mul]
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith

theorem rationalKernel_bound (z₁ z₂ z₃ : ℂ)
    (h₁ : |z₁.im| ≤ 1/2) (h₂ : |z₂.im| ≤ 1/2) (h₃ : |z₃.im| ≤ 1/2) :
    ‖rationalKernel z₁ z₂ z₃‖ ≤ 7 * Real.pi / 9 := by
  have hd (z w : ℂ) (hz : |z.im| ≤ 1/2) (hw : |w.im| ≤ 1/2) : |(z-w).im| ≤ 1 := by
    simpa only [Complex.sub_im] using (abs_sub z.im w.im).trans (by linarith)
  have h12 := hd z₁ z₂ h₁ h₂
  have h13 := hd z₁ z₃ h₁ h₃
  have h23 := hd z₂ z₃ h₂ h₃
  have hb (z : ℂ) (hz : |z.im| ≤ 1) : 3 ≤ ‖4+z^2‖ :=
    le_trans (by nlinarith [sq_nonneg z.re]) (rational_denominator_lower z hz)
  have a := hb _ h12
  have b := hb _ h13
  have c := hb _ h23
  rw [rationalKernel_reciprocal _ _ _ (rational_denominator_ne_zero _ h12)
    (rational_denominator_ne_zero _ h13) (rational_denominator_ne_zero _ h23), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hp := reciprocal_pair_bound _ _ a b
  have hq := reciprocal_pair_bound _ _ a c
  have hr := reciprocal_pair_bound _ _ b c
  have hs : ‖(12 : ℂ) / ((4+(z₁-z₂)^2)*(4+(z₁-z₃)^2)*(4+(z₂-z₃)^2))‖ ≤ 12/27 := by
    rw [norm_div, norm_mul, norm_mul]
    norm_num only [Complex.norm_ofNat]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    have hab : 9 ≤ ‖4+(z₁-z₂)^2‖ * ‖4+(z₁-z₃)^2‖ := by nlinarith
    nlinarith
  have hn := norm_add_le (1 / ((4+(z₁-z₂)^2)*(4+(z₁-z₃)^2)) +
    1 / ((4+(z₁-z₂)^2)*(4+(z₂-z₃)^2)) +
    1 / ((4+(z₁-z₃)^2)*(4+(z₂-z₃)^2)))
    (12 / ((4+(z₁-z₂)^2)*(4+(z₁-z₃)^2)*(4+(z₂-z₃)^2)))
  calc
    _ ≤ Real.pi * (1/9 + 1/9 + 1/9 + 12/27) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      exact hn.trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add hp hq)) hr)) hs)
    _ = _ := by ring

theorem rationalProfile_bound (a b e f g : ℝ)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) (hg : |g| ≤ 1/2) :
    ‖rationalProfile a b e f g‖ ≤ 7 * Real.pi / 9 := by
  apply rationalKernel_bound
  · simpa using he
  · simpa using hf
  · simpa using hg

theorem rationalProfile_swap (a b e f g : ℝ) :
    rationalProfile a b e f g = rationalProfile b a f e g := by
  unfold rationalProfile rationalKernel
  congr 1 <;> ring

theorem rationalProfile_conj (a b e f g : ℝ) :
    rationalProfile a b (-e) (-f) (-g) = star (rationalProfile a b e f g) := by
  simp [rationalProfile, rationalKernel]

theorem rationalProfile_origin : rationalProfile 0 0 0 0 0 = kernelBenchmark := by
  norm_num [rationalProfile, rationalKernel, kernelBenchmark]
  ring

theorem rationalProfile_coincident (e : ℝ) : rationalProfile 0 0 e e (-e) = kernelBenchmark := by
  simp [rationalProfile, rationalKernel, kernelBenchmark]
  ring

theorem rationalProfile_real (a b : ℝ) :
    rationalProfile a b 0 0 0 =
      ((Real.pi * (24 + (a-b)^2 + a^2 + b^2) /
        ((4+(a-b)^2)*(4+a^2)*(4+b^2)) : ℝ) : ℂ) := by
  simp [rationalProfile, rationalKernel]

theorem rational_denominator_endpoint (x : ℝ) :
    3 + x^2 ≤ ‖4 + ((x : ℂ) + Complex.I)^2‖ := by
  simpa using rational_denominator_lower ((x : ℂ) + Complex.I) (by simp)

theorem actualRationalKernel_bound (t : Fin 3 → ZeroOccurrence) :
    ‖actualRationalKernel t‖ ≤ 7 * Real.pi / 9 :=
  rationalProfile_bound _ _ _ _ _ (occurrence_displacement_lt _).le
    (occurrence_displacement_lt _).le (occurrence_displacement_lt _).le

theorem actualRealKernel_bound (t : Fin 3 → ZeroOccurrence) :
    ‖actualRealKernel t‖ ≤ 7 * Real.pi / 9 :=
  rationalProfile_bound _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)

end
end HigherCorrelations
