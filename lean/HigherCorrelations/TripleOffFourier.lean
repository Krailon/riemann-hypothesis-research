import HigherCorrelations.TripleOffFourierDefinitions
import HigherCorrelations.TripleLogGap
import HigherCorrelations.PairMeanFourierDecay

/-! UNCONDITIONAL decay of the absolutely convergent grouped off-diagonal series.
Equal frequencies are removed before applying the reciprocal logarithmic gap. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem tripleLogFrequency_difference (m n : LogGapIndex) :
    tripleLogFrequency n-tripleLogFrequency m = Real.log ((m.val:ℝ)/n.val)/(2*Real.pi) := by
  have hm : (0:ℝ)<m.val := by exact_mod_cast (show 0<m.val by have := m.property; omega)
  have hn : (0:ℝ)<n.val := by exact_mod_cast (show 0<n.val by have := n.property; omega)
  rw [Real.log_div hm.ne' hn.ne']
  unfold tripleLogFrequency
  ring

theorem tripleLogFrequency_gap_ne (m n : LogGapIndex) (h : m≠n) :
    Real.log ((m.val:ℝ)/n.val)≠0 := by
  have hm : (0:ℝ)<m.val := by exact_mod_cast (show 0<m.val by have := m.property; omega)
  have hn : (0:ℝ)<n.val := by exact_mod_cast (show 0<n.val by have := n.property; omega)
  apply abs_pos.mp
  apply tripleLogGap_nonzero _ _ hm hn
  intro he
  exact h (Subtype.ext (by exact_mod_cast he))

theorem tripleLogFourierOffTerm_bound (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0<T) (c d : LogGapIndex → ℂ)
    (p : LogGapIndex × LogGapIndex) :
    ‖tripleLogFourierOffTerm φ T c d p‖ ≤
      (fourierDerivativeL1 φ 1/T)*tripleLogGapTerm c d p := by
  classical
  by_cases hp : p.1=p.2
  · simp [tripleLogFourierOffTerm,tripleLogGapTerm,hp]
  · have hl := tripleLogFrequency_gap_ne p.1 p.2 hp
    have hf : T/(2*Real.pi)*Real.log ((p.1.val:ℝ)/p.2.val)≠0 :=
      mul_ne_zero (div_ne_zero hT.ne' (by positivity)) hl
    have hb := fourierDecay_real_bound φ 1 hφ hs _ hf
    have he : 2*Real.pi*|T/(2*Real.pi)*Real.log ((p.1.val:ℝ)/p.2.val)| =
        T*|Real.log ((p.1.val:ℝ)/p.2.val)| := by
      rw [abs_mul,abs_div,abs_of_pos hT,abs_of_pos (by positivity : 0<2*Real.pi)]
      field_simp
    rw [pow_one,he] at hb
    simp only [tripleLogFourierOffTerm,if_neg hp,tripleLogFourierTerm,norm_mul,norm_star,
      tripleLogGapTerm]
    calc
      _ ≤ (‖c p.1‖*‖d p.2‖)*(fourierDerivativeL1 φ 1/(T*|Real.log ((p.1.val:ℝ)/p.2.val)|)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

theorem tripleLogFourierOff_summable (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0<T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    Summable (fun p => ‖tripleLogFourierOffTerm φ T c d p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (tripleLogFourierOffTerm_bound φ hφ hs T hT c d)
    ((tripleLogGap_summable c d hc hd hec hed).mul_left _)

theorem tripleLogFourierOff_bound (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0<T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    ‖∑' p, tripleLogFourierOffTerm φ T c d p‖ ≤
      (fourierDerivativeL1 φ 1/T)*tripleLogGapBound c d := by
  have hm := tripleLogGap_summable c d hc hd hec hed
  calc
    _ ≤ ∑' p, ‖tripleLogFourierOffTerm φ T c d p‖ :=
      norm_tsum_le_tsum_norm (tripleLogFourierOff_summable φ hφ hs T hT c d hc hd hec hed)
    _ ≤ ∑' p, (fourierDerivativeL1 φ 1/T)*tripleLogGapTerm c d p :=
      (tripleLogFourierOff_summable φ hφ hs T hT c d hc hd hec hed).tsum_le_tsum
        (tripleLogFourierOffTerm_bound φ hφ hs T hT c d) (hm.mul_left _)
    _ = (fourierDerivativeL1 φ 1/T)*(∑' p, tripleLogGapTerm c d p) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (tripleLogGap_bound c d hc hd hec hed)
      (div_nonneg (fourierDerivativeL1_nonneg φ 1) hT.le)

end
end HigherCorrelations
