import HigherCorrelations.PairDiagonalAbel
import HigherCorrelations.PairDiagonalCumulative

/-! UNCONDITIONAL. Finite-height diagonal identity and a uniform error bound.
The infinite endpoint is not taken in this file. -/
namespace HigherCorrelations
noncomputable section
open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

theorem pairDiagonal_finite_split (X Y : ℝ) (hX : 1 ≤ X) (hXY : X ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, pairDiagonalWeight X n*(Λ n)^2) =
      (1/X^2)*(∑ n ∈ Icc 0 ⌊X⌋₊, (n:ℝ)*(Λ n)^2)+
      X^2*(∑ n ∈ Ioc ⌊X⌋₊ ⌊Y⌋₊, (Λ n)^2/(n:ℝ)^3) := by
  have hX0 : 0 ≤ X := by linarith
  have hfloor := Nat.floor_le_floor hXY
  have hs : Icc 0 ⌊Y⌋₊ = Icc 0 ⌊X⌋₊ ∪ Ioc ⌊X⌋₊ ⌊Y⌋₊ := by
    ext n; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  have hd : Disjoint (Icc 0 ⌊X⌋₊) (Ioc ⌊X⌋₊ ⌊Y⌋₊) := by
    apply disjoint_left.mpr
    intro n hn hm
    have := mem_Icc.mp hn; have := mem_Ioc.mp hm; omega
  rw [hs, sum_union hd, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl; intro n hn
    have h : (n:ℝ) ≤ X := (Nat.le_floor_iff hX0).mp (mem_Icc.mp hn).2
    simp [pairDiagonalWeight, h]; ring
  · apply sum_congr rfl; intro n hn
    have h : X < (n:ℝ) := (Nat.floor_lt hX0).mp (mem_Ioc.mp hn).1
    simp [pairDiagonalWeight, not_le_of_gt h]; ring

/-- Cancellation of the two boundary terms at X is exact. -/
theorem pairDiagonal_finite_abel (X Y : ℝ) (hX : 1 ≤ X) (hXY : X ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, pairDiagonalWeight X n*(Λ n)^2) =
      X^2*pairDiagonalCumulative Y/Y^3-
      (1/X^2)*(∫ u in (1:ℝ)..X, pairDiagonalCumulative u)+
      3*X^2*(∫ u in X..Y, pairDiagonalCumulative u/u^4) := by
  rw [pairDiagonal_finite_split X Y hX hXY, pairDiagonal_head_abel X hX,
    pairDiagonal_tail_abel X Y hX hXY]
  have hX0 : X ≠ 0 := by linarith
  field_simp
  <;> ring

theorem pairDiagonal_error_integrals (C X Y : ℝ) (hC : 0 < C) (hX : 1 ≤ X) (hXY : X ≤ Y)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ C*u) :
    |∫ u in (1:ℝ)..X, pairDiagonalCumulative u-u*Real.log u| ≤ C*X^2/2 ∧
    |∫ u in X..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4| ≤ C/(2*X^2) := by
  have hX0 : 0 < X := by linarith
  constructor
  · have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hX
      (f := fun u : ℝ => pairDiagonalCumulative u-u*Real.log u)
      (g := fun u : ℝ => C*u) (Filter.Eventually.of_forall (by
        intro u hu; rw [Real.norm_eq_abs]; exact hE u hu.1.le))
      ((continuous_const.mul continuous_id).intervalIntegrable 1 X)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_id] at hb
    exact hb.trans (by nlinarith)
  · have hc : ContinuousOn (fun u : ℝ => C/u^3) (Set.uIcc X Y) :=
      continuousOn_const.div (continuousOn_id.pow 3) (by
        intro u hu; rw [Set.uIcc_of_le hXY] at hu
        exact pow_ne_zero _ (ne_of_gt (hX0.trans_le hu.1)))
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hXY
      (f := fun u : ℝ => (pairDiagonalCumulative u-u*Real.log u)/u^4)
      (g := fun u : ℝ => C/u^3) (Filter.Eventually.of_forall (by
        intro u hu
        have hu0 : 0 < u := hX0.trans hu.1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hu0 4)]
        calc
          _ ≤ C*u/u^4 := div_le_div_of_nonneg_right (hE u (hX.trans hu.1.le)) (by positivity)
          _ = _ := by field_simp)) hc.intervalIntegrable
    have hi : (∫ u in X..Y, C/u^3) = C*(1/(2*X^2)-1/(2*Y^2)) := by
      rw [← pairDiagonal_inverse_cube_integral X Y hX0 hXY, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro u hu; dsimp; ring
    rw [Real.norm_eq_abs, hi] at hb
    exact hb.trans (by
      have hp : 0 ≤ C*(1/(2*Y^2)) := by positivity
      have he : C*(1/(2*X^2)-1/(2*Y^2)) = C/(2*X^2)-C*(1/(2*Y^2)) := by ring
      rw [he]; linarith)

/-- The finite model has an explicit upper-boundary term. -/
theorem pairDiagonal_finite_error_identity (X Y : ℝ) (hX : 1 ≤ X) (hXY : X ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, pairDiagonalWeight X n*(Λ n)^2)-
      (Real.log X+1-1/(4*X^2)-X^2*(2*Real.log Y+3)/(4*Y^2)) =
      X^2*(pairDiagonalCumulative Y-Y*Real.log Y)/Y^3-
      (1/X^2)*(∫ u in (1:ℝ)..X, pairDiagonalCumulative u-u*Real.log u)+
      3*X^2*(∫ u in X..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := hX0.trans_le hXY
  have hA1 : IntervalIntegrable pairDiagonalCumulative volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
      (pairDiagonalCumulative_integrable 1 X zero_le_one)
  have hM1 : IntervalIntegrable (fun u : ℝ => u*Real.log u) volume 1 X := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.mul (Real.continuousOn_log.mono _)
    intro u hu; rw [Set.uIcc_of_le hX] at hu; exact ne_of_gt (by linarith [hu.1])
  have hA2 : IntervalIntegrable (fun u : ℝ => pairDiagonalCumulative u/u^4) volume X Y := by
    have ha : IntervalIntegrable pairDiagonalCumulative volume X Y :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hXY).mpr
        (pairDiagonalCumulative_integrable X Y hX0.le)
    have hc : ContinuousOn (fun u : ℝ => (u^4)⁻¹) (Set.uIcc X Y) :=
      (continuousOn_id.pow 4).inv₀ (by
        intro u hu; rw [Set.uIcc_of_le hXY] at hu
        exact pow_ne_zero _ (hX0.trans_le hu.1).ne')
    simpa only [div_eq_mul_inv] using ha.mul_continuousOn hc
  have hM2 : IntervalIntegrable (fun u : ℝ => Real.log u/u^3) volume X Y := by
    apply ContinuousOn.intervalIntegrable
    have hu0 (u : ℝ) (hu : u ∈ Set.uIcc X Y) : 0 < u := by
      rw [Set.uIcc_of_le hXY] at hu; exact hX0.trans_le hu.1
    exact (Real.continuousOn_log.mono (fun u hu => (hu0 u hu).ne')).div
      (continuousOn_id.pow 3) (fun u hu => pow_ne_zero _ (hu0 u hu).ne')
  have he2 : (∫ u in X..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4) =
      (∫ u in X..Y, pairDiagonalCumulative u/u^4)-(∫ u in X..Y, Real.log u/u^3) := by
    rw [← intervalIntegral.integral_sub hA2 hM2]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u ≠ 0 := by rw [Set.uIcc_of_le hXY] at hu; linarith [hu.1]
    dsimp; field_simp <;> ring
  rw [pairDiagonal_finite_abel X Y hX hXY, intervalIntegral.integral_sub hA1 hM1,
    he2, pairDiagonal_head_integral X hX, pairDiagonal_tail_integral X Y hX0 hXY]
  field_simp
  <;> ring

/-- Uniform error for every finite upper endpoint Y>=X, ready for a justified limit. -/
theorem pairDiagonal_finite_error_bound (C X Y : ℝ) (hC : 0 < C) (hX : 1 ≤ X) (hXY : X ≤ Y)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ C*u) :
    |(∑ n ∈ Icc 0 ⌊Y⌋₊, pairDiagonalWeight X n*(Λ n)^2)-
      (Real.log X+1-1/(4*X^2)-X^2*(2*Real.log Y+3)/(4*Y^2))| ≤ 3*C := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := hX0.trans_le hXY
  obtain ⟨hhead,htail⟩ := pairDiagonal_error_integrals C X Y hC hX hXY hE
  have hb : |X^2*(pairDiagonalCumulative Y-Y*Real.log Y)/Y^3| ≤ C := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg X), abs_of_pos (pow_pos hY0 3)]
    calc
      _ ≤ X^2*(C*Y)/Y^3 := by gcongr; exact hE Y (hX.trans hXY)
      _ = C*X^2/Y^2 := by field_simp <;> ring
      _ ≤ C := (div_le_iff₀ (sq_pos_of_pos hY0)).mpr (by gcongr)
  have hh : |(1/X^2)*(∫ u in (1:ℝ)..X, pairDiagonalCumulative u-u*Real.log u)| ≤ C/2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1/X^2)]
    calc
      _ ≤ (1/X^2)*(C*X^2/2) := mul_le_mul_of_nonneg_left hhead (by positivity)
      _ = _ := by field_simp
  have ht : |3*X^2*(∫ u in X..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4)| ≤ 3*C/2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3*X^2)]
    calc
      _ ≤ 3*X^2*(C/(2*X^2)) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by field_simp
  rw [pairDiagonal_finite_error_identity X Y hX hXY]
  exact (abs_add_le _ _).trans ((add_le_add ((abs_sub _ _).trans (add_le_add hb hh)) ht).trans (by ring_nf; rfl))

end
end HigherCorrelations
