import HigherCorrelations.PairSeriesTopology
import HigherCorrelations.PairKernelEstimates
import HigherCorrelations.ScalarKernel
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! UNCONDITIONAL convergence of the actual multiplicity-preserving zero series. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pair_occurrence_displacement (i : ZeroOccurrence) : |occurrenceDisplacement i| ≤ 1/2 := by
  have h := i.1.property.2
  change 0 < (occurrenceValue i).re ∧ (occurrenceValue i).re < 1 at h
  unfold occurrenceDisplacement
  rw [abs_le]
  constructor <;> linarith

theorem pair_denominator_lower (v d : ℝ) (hd : |d| ≤ 1/2) :
    (3/4 : ℝ)*(1+v^2) ≤ ‖1+((v:ℂ)+Complex.I*d)^2‖ := by
  have h := Complex.re_le_norm (1+((v:ℂ)+Complex.I*d)^2)
  have hr : (1+((v:ℂ)+Complex.I*d)^2).re = 1+v^2-d^2 := by
    simp [pow_two, Complex.mul_re]; ring
  rw [hr] at h
  rcases abs_le.mp hd with ⟨hl,hu⟩
  nlinarith [sq_nonneg v]

theorem pairZeroTerm_bound (i : ZeroOccurrence) (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroTerm i (X,t)‖ ≤ (8/3 : ℝ)*Real.sqrt X*ordinateKernel (t-occurrenceOrdinate i) := by
  have hd := pair_occurrence_displacement i
  have hb := pair_denominator_lower (t-occurrenceOrdinate i) (occurrenceDisplacement i) hd
  have hp : 0 < 1+(t-occurrenceOrdinate i)^2 := by positivity
  have hn : 0 < ‖1+((t-occurrenceOrdinate i:ℝ)+Complex.I*occurrenceDisplacement i)^2‖ := by linarith
  have he : Real.exp (Real.log X * occurrenceDisplacement i) ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : 0<X)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (abs_le.mp hd).2 (Real.log_nonneg hX)
  have hnume : ‖(2:ℂ)*Complex.exp ((Real.log X:ℂ)*
      ((occurrenceDisplacement i:ℂ)+Complex.I*(occurrenceOrdinate i-t)))‖ =
      2*Real.exp (Real.log X*occurrenceDisplacement i) := by
    rw [norm_mul, Complex.norm_exp]
    norm_num [Complex.mul_re]
  unfold pairZeroTerm
  dsimp only
  rw [norm_div, hnume]
  calc
    _ ≤ (2*Real.sqrt X)/((3/4)*(1+(t-occurrenceOrdinate i)^2)) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hb
    _ = _ := by unfold ordinateKernel; rw [div_mul_eq_div_div]; ring

theorem pairZeroTerm_summable (X t : ℝ) (hX : 1 ≤ X) :
    Summable (fun i => ‖pairZeroTerm i (X,t)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => pairZeroTerm_bound i X t hX)
    (((zeroKernel_summable_bound.choose_spec.2 t).1).mul_left ((8/3)*Real.sqrt X))

theorem pairZeroTail_bound : ∃ C : ℝ, 0<C ∧ ∀ X t U : ℝ, 1≤X → 2*(|t|+2)≤U →
    pairZeroTail X t U ≤ C*Real.sqrt X*Real.log U/U := by
  obtain ⟨C,hC,hb⟩ := zeroKernelTail_summable_bound
  refine ⟨(32/3)*C,by positivity,fun X t U hX hU => ?_⟩
  have hu : 0<U := by linarith [abs_nonneg t]
  have hlog : 0 ≤ Real.log U := Real.log_nonneg (by linarith [abs_nonneg t])
  have hh := kernel_restricted_le_tail t (U/2) (by positivity)
    (fun i => U < |occurrenceOrdinate i|) (by
      intro i hi
      have he : |occurrenceOrdinate i| ≤ |t-occurrenceOrdinate i|+|t| := by
        simpa [abs_sub_comm] using abs_add_le (occurrenceOrdinate i-t) t
      linarith)
  have hl : Real.log (|t|+U/2+2) ≤ 2*Real.log U := by
    have h := Real.log_le_log (show 0 < |t|+U/2+2 by positivity)
      (show |t|+U/2+2 ≤ U^2 by nlinarith [abs_nonneg t])
    simpa [Real.log_pow] using h
  have hk : (∑' i : {i : ZeroOccurrence // U < |occurrenceOrdinate i|},
      ordinateKernel (t-occurrenceOrdinate i.val)) ≤ 4*C*Real.log U/U := by
    calc
      _ ≤ C*Real.log (|t|+U/2+2)/(1+U/2) := hh.2.trans (hb t (U/2) (by positivity)).2
      _ ≤ C*(2*Real.log U)/(U/2) := div_le_div₀
        (by positivity) (mul_le_mul_of_nonneg_left hl hC.le) (by positivity) (by linarith)
      _ = _ := by ring
  have hs := (pairZeroTerm_summable X t hX).subtype (fun i => U < |occurrenceOrdinate i|)
  calc
    _ ≤ ∑' i : {i : ZeroOccurrence // U < |occurrenceOrdinate i|},
        ((8/3)*Real.sqrt X)*ordinateKernel (t-occurrenceOrdinate i.val) :=
      hs.tsum_le_tsum (fun i => pairZeroTerm_bound i.val X t hX) (hh.1.mul_left _)
    _ = ((8/3)*Real.sqrt X)*(∑' i : {i : ZeroOccurrence // U < |occurrenceOrdinate i|},
        ordinateKernel (t-occurrenceOrdinate i.val)) := tsum_mul_left
    _ ≤ ((8/3)*Real.sqrt X)*(4*C*Real.log U/U) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by ring

theorem pair_kernel_rectangle (t g H : ℝ) (ht : |t| ≤ H) :
    ordinateKernel (t-g) ≤ (2+2*H^2)*ordinateKernel g := by
  have hsq : t^2 ≤ H^2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hpoly : 1+g^2 ≤ (2+2*H^2)*(1+(t-g)^2) := by
    nlinarith [sq_nonneg (t-(t-g)), sq_nonneg (t+(t-g)),
      mul_nonneg (sq_nonneg H) (sq_nonneg (t-g))]
  unfold ordinateKernel
  rw [mul_div_assoc']
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpoly)

theorem pairZero_rectangle_majorant (B H : ℝ) (hB : 1 ≤ B) :
    ∃ M : ZeroOccurrence → ℝ, Summable M ∧
      ∀ i p, p ∈ pairSeriesRectangle B H → ‖pairZeroTerm i p‖ ≤ M i := by
  let K := (8/3 : ℝ)*Real.sqrt B*(2+2*H^2)
  refine ⟨fun i => K*ordinateKernel (-occurrenceOrdinate i), ?_, ?_⟩
  · simpa using ((zeroKernel_summable_bound.choose_spec.2 0).1).mul_left K
  · intro i p hp
    have h := pairZeroTerm_bound i p.1 p.2 hp.1
    have hk := pair_kernel_rectangle p.2 (occurrenceOrdinate i) H hp.2.2
    have hs := Real.sqrt_le_sqrt hp.2.1
    calc
      _ ≤ ((8/3)*Real.sqrt B)*ordinateKernel (p.2-occurrenceOrdinate i) :=
        h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
          (ordinateKernel_nonneg _))
      _ ≤ ((8/3)*Real.sqrt B)*((2+2*H^2)*ordinateKernel (occurrenceOrdinate i)) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by simp [K, ordinateKernel]; ring

theorem pairZero_uniform_rectangle (B H : ℝ) (hB : 1≤B) :
    TendstoUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop (pairSeriesRectangle B H) := by
  obtain ⟨M,hM,hb⟩ := pairZero_rectangle_majorant B H hB
  exact tendstoUniformlyOn_tsum hM hb

theorem pairZeroTerm_continuous (i : ZeroOccurrence) : ContinuousOn (pairZeroTerm i) pairSeriesDomain := by
  apply ContinuousOn.div
  · apply continuousOn_const.mul
    apply Complex.continuous_exp.comp_continuousOn
    apply ContinuousOn.mul
    · exact Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_fst.log (fun p hp => by have : 1≤p.1 := hp; linarith))
    · fun_prop
  · fun_prop
  · intro p _
    exact scalar_denominator_ne_zero _ _ (by have := pair_occurrence_displacement i; linarith)

theorem pairZero_locallyUniform :
    TendstoLocallyUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop pairSeriesDomain :=
  pairSeries_locallyUniform pairZero_uniform_rectangle

theorem pairZeroSeries_continuous : ContinuousOn pairZeroSeries pairSeriesDomain := by
  apply pairZero_locallyUniform.continuousOn
  exact Filter.Frequently.of_forall (fun s => continuousOn_finsetSum _ (fun i _ => pairZeroTerm_continuous i))

theorem pair_occurrenceCutoff_tendsto : Tendsto occurrenceCutoff atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro s
  have h : ∀ᶠ U : ℝ in atTop, ∀ i ∈ s, i ∈ occurrenceCutoff U := by
    apply (Filter.eventually_all_finset s).mpr
    intro i _
    filter_upwards [eventually_ge_atTop |occurrenceOrdinate i|] with U hU
    exact (mem_occurrenceCutoff i U).mpr hU
  exact h

theorem pairZero_cutoff_uniform (B H : ℝ) (hB : 1≤B) :
    TendstoUniformlyOn (fun U : ℝ => fun p => ∑ i ∈ occurrenceCutoff U, pairZeroTerm i p)
      pairZeroSeries atTop (pairSeriesRectangle B H) := by
  intro u hu
  exact pair_occurrenceCutoff_tendsto.eventually (pairZero_uniform_rectangle B H hB u hu)

theorem pairZero_cutoff_locallyUniform :
    TendstoLocallyUniformlyOn (fun U : ℝ => fun p => ∑ i ∈ occurrenceCutoff U, pairZeroTerm i p)
      pairZeroSeries atTop pairSeriesDomain :=
  pairSeries_locallyUniform pairZero_cutoff_uniform

theorem pairZero_cutoff_remainder (X t U : ℝ) (hX : 1≤X) :
    ‖pairZeroSeries (X,t) - ∑ i ∈ occurrenceCutoff U, pairZeroTerm i (X,t)‖ ≤ pairZeroTail X t U := by
  classical
  have hs := pairZeroTerm_summable X t hX
  have he := hs.of_norm.sum_add_tsum_subtype_compl (occurrenceCutoff U)
  unfold pairZeroSeries
  rw [← he, add_sub_cancel_left]
  have hn := norm_tsum_le_tsum_norm (hs.subtype (fun i => i ∉ occurrenceCutoff U))
  have heq : pairZeroTail X t U = ∑' i : {i : ZeroOccurrence // i ∉ occurrenceCutoff U}, ‖pairZeroTerm i.val (X,t)‖ := by
    let tail (P : ZeroOccurrence → Prop) := ∑' i : {i // P i}, ‖pairZeroTerm i.val (X,t)‖
    change tail (fun i => U < |occurrenceOrdinate i|) = tail (fun i => i ∉ occurrenceCutoff U)
    congr 1
    funext i
    exact propext (by simp [mem_occurrenceCutoff, not_le])
  exact hn.trans_eq heq.symm

end
end HigherCorrelations
