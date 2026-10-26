import HigherCorrelations.TripleMixedFourier
import HigherCorrelations.TripleOffFourier

/-! UNCONDITIONAL exact diagonal extraction for grouped log-frequency series.
All series are absolutely convergent before the smoothing integral is exchanged. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem tripleLogFourier_summable (φ : ℝ → ℝ) (T : ℝ) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    Summable (fun p => ‖tripleLogFourierTerm φ T c d p‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun p : LogGapIndex × LogGapIndex => (‖c p.1‖*‖d p.2‖)*fourierDerivativeL1 φ 0)
  · intro p
    simp only [tripleLogFourierTerm,norm_mul,norm_star]
    exact mul_le_mul_of_nonneg_left (fourierDecay_real_mass φ _) (by positivity)
  · exact (hc.mul_of_nonneg hd (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right _

theorem tripleLogFourier_identity (φ : ℝ → ℝ) (hφ : Integrable φ)
    (T : ℝ) (hT : 0<T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    (∫ t, ((φ (t/T)/T:ℝ):ℂ)*(pairFrequencySum tripleLogFrequency c t *
      star (pairFrequencySum tripleLogFrequency d t))) =
      ∑' p, tripleLogFourierTerm φ T c d p := by
  rw [pairMeanWeighted_cross_identity tripleLogFrequency tripleLogFrequency c d hc hd (fun t => ((φ (t/T)/T:ℝ):ℂ))
    ((hφ.comp_div hT.ne').div_const T).ofReal]
  apply tsum_congr
  intro p
  rw [pairMeanFourier_normalized φ T _ hT,tripleLogFrequency_difference]
  unfold tripleLogFourierTerm
  congr 2
  ring

theorem tripleLogFourier_diagonal (φ : ℝ → ℝ) (T : ℝ) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    (∑' p, tripleLogFourierTerm φ T c d p) =
      (∑' n, c n*star (d n))*pairMeanFourier (fun u => (φ u:ℂ)) 0 +
        ∑' p, tripleLogFourierOffTerm φ T c d p := by
  classical
  let A := tripleLogFourierTerm φ T c d
  let B : LogGapIndex × LogGapIndex → ℂ := fun p => if p.1=p.2 then A p else 0
  let O := tripleLogFourierOffTerm φ T c d
  have hA := tripleLogFourier_summable φ T c d hc hd
  have hB : Summable B := hA.of_norm_bounded (fun p => by
    dsimp [B]; split_ifs <;> simp [A])
  have hO : Summable O := hA.of_norm_bounded (fun p => by
    dsimp [O,tripleLogFourierOffTerm]; split_ifs <;> simp [A])
  have hdiag : (∑' p, B p) = (∑' n, c n*star (d n))*pairMeanFourier (fun u => (φ u:ℂ)) 0 := by
    rw [hB.tsum_prod]
    have he (n : LogGapIndex) : (∑' m, B (n,m)) = c n*star (d n)*pairMeanFourier (fun u => (φ u:ℂ)) 0 := by
      simp only [B,Prod.fst,Prod.snd,tsum_ite_eq']
      have hn : (n.val:ℝ)≠0 := by exact_mod_cast (show n.val≠0 by have := n.property; omega)
      simp [A,tripleLogFourierTerm,hn]
    simp_rw [he]
    exact tsum_mul_right
  have he : (fun p => B p+O p)=A := by
    funext p
    dsimp [B,O,tripleLogFourierOffTerm,A]
    split_ifs <;> simp
  rw [← hdiag,← hB.tsum_add hO,he]

/-- The exact smoothed cross product minus its full diagonal is the signed off series. -/
theorem tripleLogFourier_off_identity (φ : ℝ → ℝ) (hφ : Integrable φ)
    (T : ℝ) (hT : 0<T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    (∫ t, ((φ (t/T)/T:ℝ):ℂ)*(pairFrequencySum tripleLogFrequency c t *
      star (pairFrequencySum tripleLogFrequency d t))) -
        (∑' n, c n*star (d n))*(∫ u, (φ u:ℂ)) =
      ∑' p, tripleLogFourierOffTerm φ T c d p := by
  rw [tripleLogFourier_identity φ hφ T hT c d hc hd,
    tripleLogFourier_diagonal φ T c d hc hd,pairMeanFourier_zero]
  abel

end
end HigherCorrelations
