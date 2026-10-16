import HigherCorrelations.PairMeanEnvelope

/-! UNCONDITIONAL pointwise interval sandwich, with closed interval endpoints.
Membership changes are controlled by the two endpoint tails. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem pairMeanScaledK_tail (δ r : ℝ) (hδ : 0 < δ) :
    (∫ u in {u : ℝ | r ≤ |u|}, pairMeanScaledK δ u) = pairMeanTail (δ*r) := by
  have hm (r : ℝ) : MeasurableSet {u : ℝ | r ≤ |u|} := isClosed_le continuous_const continuous_abs |>.measurableSet
  rw [← integral_indicator (hm r)]
  have he : (fun u => ({u : ℝ | r ≤ |u|}).indicator (pairMeanScaledK δ) u) =
      fun u => δ*(({v : ℝ | δ*r ≤ |v|}).indicator pairMeanK (δ*u)) := by
    funext u
    have hh : δ*r ≤ |δ*u| ↔ r ≤ |u| := by
      rw [abs_mul,abs_of_pos hδ,mul_le_mul_iff_right₀ hδ]
    by_cases hu : r ≤ |u|
    · rw [indicator_of_mem (show u ∈ {u : ℝ | r ≤ |u|} from hu),
        indicator_of_mem (show δ*u ∈ {v : ℝ | δ*r ≤ |v|} from hh.mpr hu)]
      rfl
    · rw [indicator_of_notMem (show u ∉ {u : ℝ | r ≤ |u|} from hu),
        indicator_of_notMem (show δ*u ∉ {v : ℝ | δ*r ≤ |v|} from fun hv => hu (hh.mp hv)),mul_zero]
  rw [he,integral_const_mul,Measure.integral_comp_mul_left,
    integral_indicator (hm (δ*r))]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr hδ),← mul_assoc,mul_inv_cancel₀ hδ.ne',one_mul,pairMeanTail]

theorem pairMeanInterval_shift_eq (T t v : ℝ) (hv0 : |v| < |t|) (hvT : |v| < |t-T|) :
    pairMeanInterval T (t-v) = pairMeanInterval T t := by
  classical
  unfold pairMeanInterval
  by_cases ht0 : 0 ≤ t
  · by_cases htT : t ≤ T
    · have h0 : 0 ≤ t-v := by
        rw [abs_of_nonneg ht0] at hv0
        linarith [le_abs_self v]
      have hT : t-v ≤ T := by
        rw [abs_of_nonpos (sub_nonpos.mpr htT)] at hvT
        linarith [neg_le_abs v]
      simp [Set.mem_Icc,ht0,htT,h0,hT]
    · have hnot : t-v ∉ Icc 0 T := by
        rw [abs_of_pos (by linarith : 0 < t-T)] at hvT
        simp only [mem_Icc,not_and_or,not_le]
        exact Or.inr (by linarith [le_abs_self v])
      rw [indicator_of_notMem hnot,indicator_of_notMem (by simp [mem_Icc,htT])]
  · have hnot : t-v ∉ Icc 0 T := by
      rw [abs_of_neg (lt_of_not_ge ht0)] at hv0
      simp only [mem_Icc,not_and_or,not_le]
      exact Or.inl (by linarith [neg_le_abs v])
    rw [indicator_of_notMem hnot,indicator_of_notMem (by simp [mem_Icc,ht0])]

theorem pairMeanInterval_shift_bound (T t v : ℝ) :
    |pairMeanInterval T (t-v)-pairMeanInterval T t| ≤
      (if |t| ≤ |v| then (1:ℝ) else 0)+(if |t-T| ≤ |v| then (1:ℝ) else 0) := by
  have hb : |pairMeanInterval T (t-v)-pairMeanInterval T t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [pairMeanInterval_nonneg T (t-v),pairMeanInterval_nonneg T t,
      pairMeanInterval_le_one T (t-v),pairMeanInterval_le_one T t]
  by_cases h0 : |t| ≤ |v|
  · split_ifs <;> linarith
  · by_cases hT : |t-T| ≤ |v|
    · simp only [if_neg h0,if_pos hT,zero_add]
      exact hb
    · rw [pairMeanInterval_shift_eq T t v (lt_of_not_ge h0) (lt_of_not_ge hT)]
      simp [h0,hT]

theorem pairMeanInterval_shift_integrable (T δ t : ℝ) (hδ : 0 < δ) :
    Integrable (fun v => pairMeanInterval T (t-v)*pairMeanScaledK δ v) := by
  apply (pairMeanScaledK_integrable δ hδ).bdd_mul (c := 1)
    (((pairMeanInterval_measurable T).comp (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with v
  change ‖pairMeanInterval T (t-v)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (pairMeanInterval_nonneg _ _)]
  exact pairMeanInterval_le_one _ _

theorem pairMeanConvolution_interval_error (T δ t : ℝ) (hδ : 0 < δ) :
    |pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t-pairMeanInterval T t| ≤
      pairMeanTail (δ*|t|)+pairMeanTail (δ*|t-T|) := by
  have hk := pairMeanScaledK_integrable δ hδ
  have hf := pairMeanInterval_shift_integrable T δ t hδ
  have he : pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t-pairMeanInterval T t =
      ∫ v, (pairMeanInterval T (t-v)-pairMeanInterval T t)*pairMeanScaledK δ v := by
    have hc := convolution_eq_swap (ContinuousLinearMap.mul ℝ ℝ)
      (f := pairMeanInterval T) (g := pairMeanScaledK δ) (μ := volume) (x := t)
    change pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t =
      ∫ v, pairMeanInterval T (t-v)*pairMeanScaledK δ v at hc
    rw [hc]
    simp_rw [sub_mul]
    rw [integral_sub hf (hk.const_mul _), integral_const_mul,pairMeanScaledK_mass δ hδ,mul_one]
  rw [he]
  have hm (r : ℝ) : MeasurableSet {v : ℝ | r ≤ |v|} := isClosed_le continuous_const continuous_abs |>.measurableSet
  let g (r v : ℝ) := ({v : ℝ | r ≤ |v|}).indicator (pairMeanScaledK δ) v
  have hg (r : ℝ) : Integrable (g r) := (integrable_indicator_iff (hm r)).mpr hk.integrableOn
  calc
    _ ≤ ∫ v, ‖(pairMeanInterval T (t-v)-pairMeanInterval T t)*pairMeanScaledK δ v‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v, g |t| v+g |t-T| v := by
      apply integral_mono (by
        simpa only [sub_mul,Pi.sub_apply] using (hf.sub (hk.const_mul (pairMeanInterval T t))).norm)
        ((hg |t|).add (hg |t-T|))
      intro v
      change ‖(pairMeanInterval T (t-v)-pairMeanInterval T t)*pairMeanScaledK δ v‖ ≤ g |t| v+g |t-T| v
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pairMeanScaledK_nonneg _ _ hδ.le)]
      have h := mul_le_mul_of_nonneg_right (pairMeanInterval_shift_bound T t v)
        (pairMeanScaledK_nonneg δ v hδ.le)
      convert h using 1
      dsimp [g,Set.indicator]
      split_ifs <;> ring
    _ = _ := by
      rw [integral_add (hg |t|) (hg |t-T|)]
      dsimp [g]
      rw [integral_indicator (hm |t|),integral_indicator (hm |t-T|),
        pairMeanScaledK_tail δ |t| hδ,pairMeanScaledK_tail δ |t-T| hδ]

theorem pairMeanEnvelope_sandwich (T δ t : ℝ) (hδ : 0 < δ) :
    pairMeanEnvelope T δ (-1) t ≤ pairMeanInterval T t ∧
      pairMeanInterval T t ≤ pairMeanEnvelope T δ 1 t := by
  have h := pairMeanConvolution_interval_error T δ t hδ
  have h0 := pairMeanTail_boundary (δ*t)
  have hT := pairMeanTail_boundary (δ*(t-T))
  rw [abs_mul,abs_of_pos hδ] at h0 hT
  rw [abs_le] at h
  unfold pairMeanEnvelope
  constructor <;> nlinarith only [h.1,h.2,h0,hT]

end
end HigherCorrelations
