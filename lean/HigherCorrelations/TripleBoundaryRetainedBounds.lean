import HigherCorrelations.TripleBoundaryRetained
import HigherCorrelations.TripleBoundaryScales
import HigherCorrelations.TripleBoundaryBox

/-! UNCONDITIONAL integrable majorants for the three retained evaluation errors. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_log_inverse (x : ℝ) (hx : 1≤x) :
    (1+Real.log x)/x^2 ≤ 1/x := by
  have hx0 : 0<x := by linarith
  have hl := Real.log_le_sub_one_of_pos hx0
  apply (div_le_iff₀ (sq_pos_of_pos hx0)).mpr
  have he : (1/x)*x^2=x := by field_simp
  rw [he]
  linarith

theorem tripleBoundary_diagonal_scale (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    tripleRetainedDiagonalScale X Y ≤ 1/X+1/Y := by
  unfold tripleRetainedDiagonalScale
  have hh := add_le_add (tripleBoundary_log_inverse Y hY) (tripleBoundary_log_inverse X hX)
  simpa only [add_comm] using hh

theorem tripleBoundary_G_frequency (B : ℝ) (hB : 1<B) (p : ℝ × ℝ)
    (hp : p ∈ tripleBoundaryBox) :
    tripleRetainedG (B^p.1) (B^p.2) ≤ 2*Real.log B*(1/B^p.1+1/B^p.2) := by
  have hb : 0<B := by linarith
  have hX := Real.one_le_rpow hB.le hp.1.1
  have hY := Real.one_le_rpow hB.le hp.2.1
  have hXp := Real.rpow_pos_of_pos hb p.1
  have hYp := Real.rpow_pos_of_pos hb p.2
  have hlog : 0≤Real.log B := (Real.log_pos hB).le
  have hx0 : 0≤Real.log (B^p.1) := Real.log_nonneg hX
  have hy0 : 0≤Real.log (B^p.2) := Real.log_nonneg hY
  have hx : Real.log (B^p.1)≤Real.log B := by rw [Real.log_rpow hb]; nlinarith [hp.1.2]
  have hy : Real.log (B^p.2)≤Real.log B := by rw [Real.log_rpow hb]; nlinarith [hp.2.2]
  rw [tripleBoundary_G_logarithms _ _ hXp hYp]
  have h1 := mul_le_mul (tripleBoundary_log_inverse (B^p.2) hY)
    (show Real.log (B^p.1)+Real.log (B^p.2)/2≤2*Real.log B by linarith)
    (by positivity : 0≤Real.log (B^p.1)+Real.log (B^p.2)/2) (by positivity : 0≤1/B^p.2)
  have h2 := mul_le_mul (tripleBoundary_log_inverse (B^p.1) hX)
    (show Real.log (B^p.2)+Real.log (B^p.1)/2≤2*Real.log B by linarith)
    (by positivity : 0≤Real.log (B^p.2)+Real.log (B^p.1)/2) (by positivity : 0≤1/B^p.1)
  convert add_le_add h1 h2 using 1 <;> ring

theorem tripleBoundary_resonance_scale (Z : ℝ) (hZ : 1≤Z) :
    tripleResonanceScale Z ≤ 3456*Z^(-(1/4:ℝ)) := by
  have hz : 0<Z := by linarith
  have hw : 0<2*Z := by positivity
  have hl0 : 0≤Real.log (2*Z) := Real.log_nonneg (by linarith)
  have hl : Real.log (2*Z)≤12*(2*Z)^(1/12:ℝ) := by
    have hh := Real.log_le_rpow_div hw.le (show (0:ℝ)<1/12 by norm_num)
    linarith
  have hc : Real.log (2*Z)^3≤1728*(2*Z)^(1/4:ℝ) := by
    have he := pow_le_pow_left₀ hl0 hl 3
    rw [mul_pow,← Real.rpow_natCast ((2*Z)^(1/12:ℝ)),← Real.rpow_mul hw.le] at he
    norm_num at he ⊢
    exact he
  have htwo : (2:ℝ)^(1/4:ℝ)≤2 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (show (1/4:ℝ)≤1 by norm_num) using 1
    exact (Real.rpow_one 2).symm
  have hc' : Real.log (2*Z)^3≤3456*Z^(1/4:ℝ) := by
    apply hc.trans
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hz.le]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hz.le (1/4:ℝ))) (by norm_num : (0:ℝ)≤1728)
    convert hh using 1 <;> ring
  unfold tripleResonanceScale
  apply (div_le_div_of_nonneg_right hc' (Real.sqrt_nonneg Z)).trans_eq
  rw [Real.sqrt_eq_rpow, mul_div_assoc,← Real.rpow_sub hz]
  norm_num

end
end HigherCorrelations
