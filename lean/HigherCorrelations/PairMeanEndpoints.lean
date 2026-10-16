import HigherCorrelations.PairMeanPrimeBridge

/-! UNCONDITIONAL endpoint and degenerate-frequency checks for the mean-value input. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairMeanValue_unit (a : ℝ) (z : ℂ) (T : ℝ) :
    (∫ t in (0:ℝ)..T, ‖pairFrequencySum (fun _ : Unit => a) (fun _ => z) t‖^2) = T*‖z‖^2 := by
  simp [pairFrequencySum,norm_mul,pairMeanCharacter_norm]

theorem pairMeanValue_empty (μ : Empty → ℝ) (c : Empty → ℂ) (T : ℝ) :
    (∫ t in (0:ℝ)..T, ‖pairFrequencySum μ c t‖^2) = 0 ∧
      pairFrequencyDiagonal c = 0 ∧ pairFrequencyNearby μ c (1/2) = 0 := by
  simp [pairFrequencySum,pairFrequencyDiagonal,pairFrequencyNearby]

theorem pairMeanValue_minimal_height {ι : Type*} [Countable ι]
    (μ : ι → ℝ) (hμ : Function.Injective μ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) :
    |(∫ t in (0:ℝ)..1, ‖pairFrequencySum μ c t‖^2)-pairFrequencyDiagonal c| ≤
      1024*pairFrequencyDiagonal c+1025*pairFrequencyNearby μ c (1/2) := by
  convert pairMeanValue_explicit μ hμ c hc 1 (1/2) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

theorem pairMeanPrimeCoefficient_one (X : ℝ) : pairMeanPrimeCoefficient X 0 = 0 := by
  simp [pairMeanPrimeCoefficient]

theorem pairMeanPrime_endpoint (T δ : ℝ) (hT : 1 ≤ T)
    (hδlo : 1/(2*T) ≤ δ) (hδhi : δ ≤ 1/2) :
    |(∫ t in (0:ℝ)..T, ‖pairPrimeSeries (1,t)‖^2)-T*pairMeanPrimeDiagonal 1| ≤
      512/δ*pairMeanPrimeDiagonal 1+1025*T*pairMeanPrimeNearby 1 δ :=
  pairMeanPrime_meanvalue 1 T δ (by norm_num) hT hδlo hδhi

end
end HigherCorrelations
