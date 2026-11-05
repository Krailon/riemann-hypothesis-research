import HigherCorrelations.ProfileMicroscopicDefinitions
import HigherCorrelations.RationalKernelBounds

/-! UNCONDITIONAL explicit gap variation on the closed horizontal cube.
No derivative or zero-count constant is used. -/
namespace HigherCorrelations
noncomputable section

theorem profileGapFactor_denominator_ne (x h : ℝ) (hh : |h|≤1) :
    4+((x:ℂ)-Complex.I*h)^2≠0 := by
  apply rational_denominator_ne_zero
  simpa using hh

theorem profileGapFactor_norm_bound (x h : ℝ) (hh : |h|≤1) :
    ‖profileGapFactor x h‖≤(1:ℝ)/3 := by
  have hb := rational_denominator_lower ((x:ℂ)-Complex.I*h) (by simpa using hh)
  have hl : 3≤‖4+((x:ℂ)-Complex.I*h)^2‖ := by nlinarith [sq_nonneg (((x:ℂ)-Complex.I*h).re)]
  rw [profileGapFactor,norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hl

theorem profileGapFactor_difference (x h : ℝ) (hh : |h|≤1) :
    ‖profileGapFactor x h-profileGapFactor 0 h‖≤(|x|+2)*|x|/9 := by
  let A : ℂ := 4+((x:ℂ)-Complex.I*h)^2
  let B : ℂ := 4+((0:ℂ)-Complex.I*h)^2
  have ha : ‖A⁻¹‖≤(1:ℝ)/3 := profileGapFactor_norm_bound x h hh
  have hb : ‖B⁻¹‖≤(1:ℝ)/3 := profileGapFactor_norm_bound 0 h hh
  have hm : ‖B-A‖≤(|x|+2)*|x| := by
    have he : B-A=(x:ℂ)*(2*Complex.I*h-x) := by dsimp [A,B]; ring
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hi : ‖2*Complex.I*(h:ℂ)-(x:ℂ)‖≤2+|x| := by
      have hn := norm_sub_le (2*Complex.I*(h:ℂ)) (x:ℂ)
      simp only [norm_mul,Complex.norm_ofNat,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,mul_one] at hn
      linarith
    have hd := mul_le_mul_of_nonneg_left hi (abs_nonneg x)
    simpa only [mul_comm,add_comm] using hd
  change ‖A⁻¹-B⁻¹‖≤_
  have hA : A≠0 := profileGapFactor_denominator_ne x h hh
  have hB : B≠0 := by simpa only [B,Complex.ofReal_zero] using profileGapFactor_denominator_ne 0 h hh
  rw [inv_sub_inv' hA hB,norm_mul,norm_mul]
  calc
    _ ≤ (1/3:ℝ)*((|x|+2)*|x|)*(1/3) := by gcongr
    _ = _ := by ring

private theorem pair_product_difference (p q p' q' : ℂ)
    (hp' : ‖p'‖≤(1:ℝ)/3) (hq : ‖q‖≤(1:ℝ)/3) :
    ‖p*q-p'*q'‖≤(‖p-p'‖+‖q-q'‖)/3 := by
  have he : p*q-p'*q'=(p-p')*q+p'*(q-q') := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hq (norm_nonneg (p-p'))
  have h2 := mul_le_mul_of_nonneg_right hp' (norm_nonneg (q-q'))
  linarith

private theorem triple_product_difference (p q r p' q' r' : ℂ)
    (hp' : ‖p'‖≤(1:ℝ)/3) (hq : ‖q‖≤(1:ℝ)/3)
    (hq' : ‖q'‖≤(1:ℝ)/3) (hr : ‖r‖≤(1:ℝ)/3) :
    ‖p*q*r-p'*q'*r'‖≤(‖p-p'‖+‖q-q'‖+‖r-r'‖)/9 := by
  have he : p*q*r-p'*q'*r'=(p*q-p'*q')*r+(p'*q')*(r-r') := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hpair := pair_product_difference p q p' q' hp' hq
  have h1 : ‖p*q-p'*q'‖*‖r‖≤((‖p-p'‖+‖q-q'‖)/3)*(1/3) := by gcongr
  have h2 : ‖p'‖*‖q'‖*‖r-r'‖≤(1/3:ℝ)*(1/3)*‖r-r'‖ := by gcongr
  linarith

theorem profileReciprocalSum_difference (p q r p' q' r' : ℂ)
    (hp' : ‖p'‖≤(1:ℝ)/3) (hq : ‖q‖≤(1:ℝ)/3)
    (hq' : ‖q'‖≤(1:ℝ)/3) (hr : ‖r‖≤(1:ℝ)/3) :
    ‖profileReciprocalSum p q r-profileReciprocalSum p' q' r'‖ ≤
      2*(‖p-p'‖+‖q-q'‖+‖r-r'‖) := by
  have he : profileReciprocalSum p q r-profileReciprocalSum p' q' r' =
      ((p*q-p'*q')+(p*r-p'*r')+(q*r-q'*r'))+12*(p*q*r-p'*q'*r') := by
    unfold profileReciprocalSum
    ring
  rw [he]
  have h1 := pair_product_difference p q p' q' hp' hq
  have h2 := pair_product_difference p r p' r' hp' hr
  have h3 := pair_product_difference q r q' r' hq' hr
  have h4 := triple_product_difference p q r p' q' r' hp' hq hq' hr
  have ht : ‖((p*q-p'*q')+(p*r-p'*r')+(q*r-q'*r'))+12*(p*q*r-p'*q'*r')‖ ≤
      (‖p*q-p'*q'‖+‖p*r-p'*r'‖+‖q*r-q'*r'‖)+12*‖p*q*r-p'*q'*r'‖ := by
    calc
      _ ≤ ‖(p*q-p'*q')+(p*r-p'*r')+(q*r-q'*r')‖+‖12*(p*q*r-p'*q'*r')‖ := norm_add_le _ _
      _ ≤ (‖p*q-p'*q'‖+‖p*r-p'*r'‖+‖q*r-q'*r'‖)+12*‖p*q*r-p'*q'*r'‖ := by
        rw [norm_mul,Complex.norm_ofNat]
        exact add_le_add
          ((norm_add_le ((p*q-p'*q')+(p*r-p'*r')) (q*r-q'*r')).trans
            (add_le_add (norm_add_le (p*q-p'*q') (p*r-p'*r')) le_rfl)) le_rfl
  linarith

end
end HigherCorrelations
