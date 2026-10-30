import HigherCorrelations.SignedSeriesDefinitions
import HigherCorrelations.PairZeroConvergence

/-! UNCONDITIONAL absolute, locally uniform convergence for every positive base.
No prime-side identity at bases less than one is used. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pairZeroTerm_positive_bound (i : ZeroOccurrence) (X t : ℝ) :
    ‖pairZeroTerm i (X,t)‖ ≤ (8/3:ℝ)*Real.exp (|Real.log X|/2)*
      ordinateKernel (t-occurrenceOrdinate i) := by
  have hd := pair_occurrence_displacement i
  have hb := pair_denominator_lower (t-occurrenceOrdinate i) (occurrenceDisplacement i) hd
  have hp : 0 < 1+(t-occurrenceOrdinate i)^2 := by positivity
  have hn : 0 < ‖1+((t-occurrenceOrdinate i:ℝ)+Complex.I*occurrenceDisplacement i)^2‖ := by linarith
  have he : Real.exp (Real.log X*occurrenceDisplacement i) ≤ Real.exp (|Real.log X|/2) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hd (abs_nonneg (Real.log X))
    have h' := le_abs_self (Real.log X*occurrenceDisplacement i)
    rw [abs_mul] at h'
    nlinarith only [h,h']
  have hnume : ‖(2:ℂ)*Complex.exp ((Real.log X:ℂ)*
      ((occurrenceDisplacement i:ℂ)+Complex.I*(occurrenceOrdinate i-t)))‖ =
      2*Real.exp (Real.log X*occurrenceDisplacement i) := by
    rw [norm_mul,Complex.norm_exp]
    norm_num [Complex.mul_re]
  unfold pairZeroTerm
  dsimp only
  rw [norm_div,hnume]
  calc
    _ ≤ (2*Real.exp (|Real.log X|/2))/((3/4)*(1+(t-occurrenceOrdinate i)^2)) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hb
    _ = _ := by unfold ordinateKernel; rw [div_mul_eq_div_div]; ring

theorem pairZeroTerm_positive_summable (X t : ℝ) :
    Summable (fun i => ‖pairZeroTerm i (X,t)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => pairZeroTerm_positive_bound i X t)
    (((zeroKernel_summable_bound.choose_spec.2 t).1).mul_left ((8/3)*Real.exp (|Real.log X|/2)))

theorem signedSeries_log_bound (a b x : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ max |Real.log a| |Real.log b| := by
  have hx := ha.trans_le hax
  have hlo := Real.log_le_log ha hax
  have hhi := Real.log_le_log hx hxb
  apply abs_le.mpr
  constructor
  · have hh := neg_abs_le (Real.log a)
    have hm := le_max_left |Real.log a| |Real.log b|
    linarith
  · exact hhi.trans ((le_abs_self _).trans (le_max_right _ _))

theorem signedSeries_rectangle_majorant (a b H : ℝ) (ha : 0 < a) :
    ∃ M : ZeroOccurrence → ℝ, Summable M ∧
      ∀ i p, p ∈ signedSeriesRectangle a b H → ‖pairZeroTerm i p‖ ≤ M i := by
  let K := (8/3:ℝ)*Real.exp (max |Real.log a| |Real.log b|/2)*(2+2*H^2)
  refine ⟨fun i => K*ordinateKernel (-occurrenceOrdinate i),?_,?_⟩
  · simpa using ((zeroKernel_summable_bound.choose_spec.2 0).1).mul_left K
  · intro i p hp
    have h := pairZeroTerm_positive_bound i p.1 p.2
    have hk := pair_kernel_rectangle p.2 (occurrenceOrdinate i) H hp.2.2
    have hs := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (signedSeries_log_bound a b p.1 ha hp.1 hp.2.1) (by norm_num : (0:ℝ) ≤ 2))
    calc
      _ ≤ ((8/3)*Real.exp (max |Real.log a| |Real.log b|/2))*ordinateKernel (p.2-occurrenceOrdinate i) :=
        h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (ordinateKernel_nonneg _))
      _ ≤ ((8/3)*Real.exp (max |Real.log a| |Real.log b|/2))*
          ((2+2*H^2)*ordinateKernel (occurrenceOrdinate i)) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by simp [K,ordinateKernel]; ring

theorem signedSeries_uniform_rectangle (a b H : ℝ) (ha : 0 < a) :
    TendstoUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop (signedSeriesRectangle a b H) := by
  obtain ⟨M,hM,hb⟩ := signedSeries_rectangle_majorant a b H ha
  exact tendstoUniformlyOn_tsum hM hb

theorem signedSeries_norm_uniform_rectangle (a b H : ℝ) (ha : 0<a) :
    TendstoUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, ‖pairZeroTerm i p‖)
      (fun p => ∑' i, ‖pairZeroTerm i p‖) atTop (signedSeriesRectangle a b H) := by
  obtain ⟨M,hM,hb⟩ := signedSeries_rectangle_majorant a b H ha
  exact tendstoUniformlyOn_tsum hM (fun i p hp => by simpa only [norm_norm] using hb i p hp)

theorem signedSeriesRectangle_nhds (p : ℝ × ℝ) (hp : p ∈ signedSeriesDomain) :
    signedSeriesRectangle (p.1/2) (p.1+1) (|p.2|+1) ∈ 𝓝[signedSeriesDomain] p := by
  have hp0 : 0 < p.1 := hp
  have ha : ∀ᶠ q : ℝ × ℝ in 𝓝 p, p.1/2 < q.1 :=
    (continuous_fst.tendsto p).eventually (lt_mem_nhds (by linarith))
  have hb : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < p.1+1 :=
    (continuous_fst.tendsto p).eventually (gt_mem_nhds (by linarith))
  have hh : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |q.2| < |p.2|+1 :=
    (continuous_snd.abs.tendsto p).eventually (gt_mem_nhds (by linarith))
  filter_upwards [nhdsWithin_le_nhds ha,nhdsWithin_le_nhds hb,nhdsWithin_le_nhds hh] with q hqa hqb hqh
  exact ⟨hqa.le,hqb.le,hqh.le⟩

theorem signedSeries_locallyUniform :
    TendstoLocallyUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, pairZeroTerm i p)
      pairZeroSeries atTop signedSeriesDomain := by
  intro u hu p hp
  exact ⟨signedSeriesRectangle (p.1/2) (p.1+1) (|p.2|+1),signedSeriesRectangle_nhds p hp,
    signedSeries_uniform_rectangle _ _ _ (by have : 0 < p.1 := hp; positivity) u hu⟩

theorem signedSeries_norm_locallyUniform :
    TendstoLocallyUniformlyOn (fun s : Finset ZeroOccurrence => fun p => ∑ i ∈ s, ‖pairZeroTerm i p‖)
      (fun p => ∑' i, ‖pairZeroTerm i p‖) atTop signedSeriesDomain := by
  intro u hu p hp
  exact ⟨signedSeriesRectangle (p.1/2) (p.1+1) (|p.2|+1),signedSeriesRectangle_nhds p hp,
    signedSeries_norm_uniform_rectangle _ _ _ (by have : 0<p.1 := hp; positivity) u hu⟩

theorem pairZeroTerm_positive_continuous (i : ZeroOccurrence) :
    ContinuousOn (pairZeroTerm i) signedSeriesDomain := by
  apply ContinuousOn.div
  · apply continuousOn_const.mul
    apply Complex.continuous_exp.comp_continuousOn
    apply ContinuousOn.mul
    · exact Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_fst.log (fun p hp => (show 0 < p.1 from hp).ne'))
    · fun_prop
  · fun_prop
  · intro p _
    exact scalar_denominator_ne_zero _ _ (by have := pair_occurrence_displacement i; linarith)

theorem signedSeries_continuous : ContinuousOn pairZeroSeries signedSeriesDomain := by
  apply signedSeries_locallyUniform.continuousOn
  exact Filter.Frequently.of_forall (fun s => continuousOn_finsetSum _
    (fun i _ => pairZeroTerm_positive_continuous i))

end
end HigherCorrelations
