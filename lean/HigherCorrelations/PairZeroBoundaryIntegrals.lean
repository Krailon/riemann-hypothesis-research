import HigherCorrelations.PairZeroEnvelope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! UNCONDITIONAL boundary profiles. All improper integrals have separately
proved integrability; adding or removing an endpoint is a null-set operation. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem pairZeroBoundaryProfile_integrable (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (pairZeroBoundaryProfile T) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  unfold pairZeroBoundaryProfile
  apply ContinuousOn.add <;> apply ContinuousOn.div continuousOn_const
  · exact continuousOn_const.add continuousOn_id
  · intro t ht
    rw [Set.uIcc_of_le hT] at ht
    linarith [ht.1]
  · exact (continuousOn_const.add continuousOn_const).sub continuousOn_id
  · intro t ht
    rw [Set.uIcc_of_le hT] at ht
    linarith [ht.2]

theorem pairZeroBoundaryProfile_integral (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, pairZeroBoundaryProfile T t) = 2*Real.log (1+T) := by
  have hd (t : ℝ) (ht : t ∈ Set.uIcc 0 T) :
      HasDerivAt (fun u : ℝ => Real.log (1+u)-Real.log (1+T-u))
        (pairZeroBoundaryProfile T t) t := by
    rw [Set.uIcc_of_le hT] at ht
    have hl := (Real.hasDerivAt_log (show 1+t ≠ 0 by linarith [ht.1])).comp t
      ((hasDerivAt_id t).const_add 1)
    have hr := (Real.hasDerivAt_log (show 1+T-t ≠ 0 by linarith [ht.2])).comp t
      ((hasDerivAt_const t (1+T)).sub (hasDerivAt_id t))
    convert hl.sub hr using 1 <;> (try funext u) <;> dsimp [pairZeroBoundaryProfile] <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (pairZeroBoundaryProfile_integrable T hT)
  simpa [two_mul] using he

theorem pairZero_tail_profile (a : ℝ) :
    IntegrableOn (fun t : ℝ => (1+t-a)⁻¹^2) (Set.Ioi a) ∧
      (∫ t in Set.Ioi a, (1+t-a)⁻¹^2) = 1 := by
  have hd (t : ℝ) (ht : t ∈ Set.Ici a) :
      HasDerivAt (fun u : ℝ => -(1+u-a)⁻¹) ((1+t-a)⁻¹^2) t := by
    have hn : 1+t-a ≠ 0 := by have hh : a ≤ t := ht; linarith
    convert ((((hasDerivAt_id t).const_add 1).sub_const a).inv hn).neg using 1 <;>
      (try funext u) <;> dsimp <;> simp only [inv_pow] <;> ring
  have hp (t : ℝ) (_ht : t ∈ Set.Ioi a) : 0 ≤ (1+t-a)⁻¹^2 := sq_nonneg _
  have ht : Tendsto (fun t : ℝ => -(1+t-a)⁻¹) atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => 1+t-a) atTop atTop :=
      by
        convert tendsto_atTop_add_const_right atTop (1-a) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop) using 1 <;> (try funext t) <;> simp only [id_eq] <;> ring
    simpa using (tendsto_inv_atTop_zero.comp hh).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp ht, ?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg' hd hp ht

theorem pairZero_left_profile :
    IntegrableOn (fun t : ℝ => (1-t)⁻¹^2) (Set.Iio 0) ∧
      (∫ t in Set.Iio (0:ℝ), (1-t)⁻¹^2) = 1 := by
  obtain ⟨hi,he⟩ := pairZero_tail_profile 0
  have hcomp := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg
    (volume : Measure ℝ)) (Homeomorph.neg ℝ).measurableEmbedding).2 hi
  have hm : IntegrableOn (fun t : ℝ => (1-t)⁻¹^2) (Set.Iio 0) := by
    simpa [Function.comp_def,sub_eq_add_neg] using hcomp
  refine ⟨hm, ?_⟩
  rw [← integral_Iic_eq_integral_Iio]
  have hh := integral_comp_neg_Iic 0 (fun t : ℝ => (1+t-0)⁻¹^2)
  simpa [sub_eq_add_neg] using hh.trans (by simpa using he)

theorem pairZeroExtensionProfile_left (T t : ℝ) (hT : 0 ≤ T) (ht : t ≤ 0) :
    pairZeroExtensionProfile T t = (1-t)⁻¹^2 := by
  unfold pairZeroExtensionProfile heightIntervalDistance
  rw [max_eq_left (show t-T ≤ -t by linarith),max_eq_right (by linarith)]
  rfl

theorem pairZeroExtensionProfile_right (T t : ℝ) (hT : 0 ≤ T) (ht : T ≤ t) :
    pairZeroExtensionProfile T t = (1+t-T)⁻¹^2 := by
  unfold pairZeroExtensionProfile heightIntervalDistance
  rw [max_eq_right (show -t ≤ t-T by linarith),max_eq_right (by linarith)]
  congr 2 <;> ring

theorem pairZeroExtensionProfile_integral (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (pairZeroExtensionProfile T) (Set.Icc 0 T)ᶜ ∧
      (∫ t in (Set.Icc (0:ℝ) T)ᶜ, pairZeroExtensionProfile T t) = 2 := by
  obtain ⟨hli,hle⟩ := pairZero_left_profile
  obtain ⟨hri,hre⟩ := pairZero_tail_profile T
  have hl : IntegrableOn (pairZeroExtensionProfile T) (Set.Iio 0) :=
    hli.congr_fun (fun t ht => (pairZeroExtensionProfile_left T t hT ht.le).symm) measurableSet_Iio
  have hr : IntegrableOn (pairZeroExtensionProfile T) (Set.Ioi T) :=
    hri.congr_fun (fun t ht => (pairZeroExtensionProfile_right T t hT ht.le).symm) measurableSet_Ioi
  have hc : (Set.Icc (0:ℝ) T)ᶜ = Set.Iio 0 ∪ Set.Ioi T := by
    ext t
    simp only [Set.mem_compl_iff,Set.mem_Icc,not_and_or,not_le,Set.mem_union,Set.mem_Iio,Set.mem_Ioi]
  rw [hc]
  refine ⟨hl.union hr, ?_⟩
  rw [setIntegral_union (Set.disjoint_left.mpr (by intro t ht hu; exact (not_lt_of_ge (hT.trans hu.le)) ht))
    measurableSet_Ioi hl hr]
  have he₁ : (∫ t in Set.Iio (0:ℝ), pairZeroExtensionProfile T t) = 1 := by
    rw [← hle]
    exact setIntegral_congr_fun measurableSet_Iio (fun t ht => pairZeroExtensionProfile_left T t hT ht.le)
  have he₂ : (∫ t in Set.Ioi T, pairZeroExtensionProfile T t) = 1 := by
    rw [← hre]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => pairZeroExtensionProfile_right T t hT ht.le)
  rw [he₁,he₂]
  norm_num

end
end HigherCorrelations
