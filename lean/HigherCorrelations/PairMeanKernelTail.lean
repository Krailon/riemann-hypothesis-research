import HigherCorrelations.PairMeanKernelMass
import HigherCorrelations.PairMeanBoundaryLower
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! UNCONDITIONAL tail control used to sandwich the interval indicator. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem pairMeanK_even (u : ℝ) : pairMeanK (-u) = pairMeanK u := by
  simp only [pairMeanK, neg_div, pairMeanSinc_even]

theorem pairMeanK_decay (u : ℝ) (hu : 0 < u) : pairMeanK u ≤ 12/(Real.pi^4*u^4) := by
  have hs := pairMeanSinc_abs_decay (u/2) (by positivity)
  rw [abs_of_pos (by positivity : (0:ℝ) < u/2)] at hs
  have hp := pow_le_pow_left₀ (abs_nonneg (pairMeanSinc (u/2))) hs 4
  rw [pow_abs, abs_of_nonneg (by positivity : 0 ≤ pairMeanSinc (u/2)^4)] at hp
  calc
    pairMeanK u ≤ (3/4:ℝ)*(1/(Real.pi*(u/2)))^4 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 12/(Real.pi^4*u^4) := by field_simp; ring

theorem pairMeanTail_le_one (r : ℝ) : pairMeanTail r ≤ 1 := by
  rw [← pairMeanK_mass]
  exact setIntegral_le_integral pairMeanK_integrable (Filter.Eventually.of_forall pairMeanK_nonneg)

theorem pairMeanTail_half (r : ℝ) (hr : 0 < r) :
    pairMeanTail r = 2*∫ u in Ioi r, pairMeanK u := by
  have he : {u : ℝ | r ≤ |u|} = Iic (-r) ∪ Ici r := by
    ext u
    simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici, le_abs]
    constructor
    · rintro (h|h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h|h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hd : Disjoint (Iic (-r)) (Ici r) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    simp only [mem_Iic, mem_Ici] at hu hv
    linarith
  rw [pairMeanTail, he, setIntegral_union hd measurableSet_Ici
    pairMeanK_integrable.integrableOn pairMeanK_integrable.integrableOn,
    integral_Ici_eq_integral_Ioi]
  have hn : (∫ u in Iic (-r), pairMeanK u) = ∫ u in Ioi r, pairMeanK u := by
    have h := integral_comp_neg_Iic (f := pairMeanK) (c := -r)
    simpa only [pairMeanK_even, neg_neg] using h
  rw [hn]
  ring

theorem pairMeanTail_decay (r : ℝ) (hr : 0 < r) :
    pairMeanTail r ≤ 8/(Real.pi^4*r^3) := by
  have hi : IntegrableOn (fun u : ℝ => u^(-4:ℝ)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  have hb : (∫ u in Ioi r, pairMeanK u) ≤ ∫ u in Ioi r, (12/Real.pi^4)*u^(-4:ℝ) := by
    apply setIntegral_mono_on pairMeanK_integrable.integrableOn (hi.const_mul _) measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := hr.trans hu
    convert pairMeanK_decay u hu0 using 1
    rw [Real.rpow_neg hu0.le]
    norm_num
    ring
  have he : (∫ u in Ioi r, (12/Real.pi^4)*u^(-4:ℝ)) = 4/(Real.pi^4*r^3) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-4:ℝ) < -1) hr]
    norm_num only [show (-4:ℝ)+1 = -3 by norm_num]
    rw [Real.rpow_neg hr.le]
    norm_num
    field_simp
    ring
  rw [he] at hb
  rw [pairMeanTail_half r hr]
  calc
    2*(∫ u in Ioi r, pairMeanK u) ≤ 2*(4/(Real.pi^4*r^3)) := by linarith
    _ = 8/(Real.pi^4*r^3) := by ring

theorem pairMeanTail_boundary (u : ℝ) : pairMeanTail |u| ≤ 64*pairMeanB u := by
  have hb := pairMeanB_lower u
  have hpi : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hpi1 : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  by_cases hu : |u| ≤ 1
  · have hu2 : u^2 ≤ 1 := by nlinarith [sq_abs u,abs_nonneg u]
    have hd : Real.pi^2*(1+u^2) ≤ 32 := by nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hu2)]
    have hb' := (div_le_iff₀ (by positivity : 0 < Real.pi^2*(1+u^2))).mp hb
    have h1 : 1 ≤ 64*pairMeanB u := by
      nlinarith [pairMeanB_nonneg u,mul_nonneg (pairMeanB_nonneg u) (sub_nonneg.mpr hd)]
    exact (pairMeanTail_le_one _).trans h1
  · have hu1 : 1 < |u| := lt_of_not_ge hu
    have hn : 0 < |u| := lt_trans zero_lt_one hu1
    have ht := pairMeanTail_decay |u| hn
    have hb' := (div_le_iff₀ (by positivity : 0 < Real.pi^2*(1+u^2))).mp hb
    apply ht.trans
    apply (div_le_iff₀ (by positivity : 0 < Real.pi^4*|u|^3)).mpr
    have hu2 : 1 ≤ u^2 := by nlinarith [sq_abs u]
    have hb0 := pairMeanB_nonneg u
    have hu3 : u^2 ≤ |u|^3 := by nlinarith [sq_abs u, mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1.le)]
    have hp4 : Real.pi^2 ≤ Real.pi^4 := by nlinarith [sq_nonneg (Real.pi^2-1)]
    have hmul : Real.pi^2*u^2 ≤ Real.pi^4*|u|^3 :=
      mul_le_mul hp4 hu3 (sq_nonneg u) (by positivity)
    have hm := mul_le_mul_of_nonneg_left hmul hb0
    have hm2 := mul_nonneg hb0 (mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hu2))
    nlinarith only [hb', hm, hm2]

end
end HigherCorrelations
