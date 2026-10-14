import HigherCorrelations.PairExactDefinitions
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-! Definition-only theorem specifications. Intentional unfinished challenge proofs;
solution modules never import this file. Assumptions: UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

theorem pairContour_right_integrable (X t : ℝ) (hX : 0 < X) :
    Integrable (fun v : ℝ => pairContourIntegrand X t (5/2+(v:ℂ)*I)) := by sorry

theorem pairContour_simple_poles (X t : ℝ) (hX : 0 < X) :
    HasSimplePolesOn (pairContourIntegrand X t) Set.univ := by sorry

theorem pairContour_residue_zero (X t : ℝ) (i : ZeroOccurrence) :
    residue (pairContourIntegrand X t) (occurrenceValue i) =
      (zeroMultiplicity i.1 : ℂ)*pairZeroTerm i (X,t) := by sorry

theorem pairContour_residue_pole (X t : ℝ) :
    residue (pairContourIntegrand X t) 1 = -pairPoleCorrection (X,t) := by sorry

theorem pairContour_residue_plus (X t : ℝ) (hX : 0 < X) :
    residue (pairContourIntegrand X t) (pairSpectralPoint t+1) =
      -(X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1) /
        riemannZeta (pairSpectralPoint t+1)) := by sorry

theorem pairContour_residue_minus (X t : ℝ) (hX : 0 < X) :
    residue (pairContourIntegrand X t) (pairSpectralPoint t-1) =
      pairShiftCorrection (X,t) := by sorry

theorem pairEulerContour_integral_hasSum (X t : ℝ) (hX : 0 < X) :
    HasSum (fun n => ∫ v : ℝ, pairEulerTerm n (5/2+(v:ℂ)*Complex.I) *
      pairContourKernel X t (5/2+(v:ℂ)*Complex.I))
      (∫ v : ℝ, pairContourIntegrand X t (5/2+(v:ℂ)*Complex.I)) := by sorry

theorem pairEulerSeries (z : ℂ) (hz : 1 < z.re) :
    (∑' n, pairEulerTerm n z) = -deriv riemannZeta z / riemannZeta z := by sorry

theorem pairExact_endpoint (t : ℝ) :
    pairZeroSeries (1,t) = -pairPrimeSeries (1,t)-pairShiftCorrection (1,t)+
      pairPoleCorrection (1,t)+pairTrivialCorrection (1,t) := by sorry

theorem pairExact_formula (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroSeries (X,t) = -pairPrimeSeries (X,t)-pairShiftCorrection (X,t)+
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by sorry

theorem pairExact_interior (X t : ℝ) (hX : 1 < X) :
    pairZeroSeries (X,t) = -pairPrimeSeries (X,t)-pairShiftCorrection (X,t)+
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by sorry

theorem pairGoodHeight_sequence :
    ∃ (C : ℝ) (U : ℕ → ℝ), 0 < C ∧
      (∀ n : ℕ, (n:ℝ)+2 < U n ∧ U n < (n:ℝ)+3) ∧
      Filter.Tendsto U Filter.atTop Filter.atTop ∧
      ∀ (n : ℕ) (i : ZeroOccurrence),
        1/(C*Real.log ((n:ℝ)+6)) ≤ |U n-occurrenceOrdinate i| ∧
        1/(C*Real.log ((n:ℝ)+6)) ≤ |-U n-occurrenceOrdinate i| := by sorry

theorem pairZeta_goodHeight_power (M : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (H U σ : ℝ), 2*(M:ℝ)+6 ≤ H → H ≤ |U| → |U| ≤ H+1 →
      -(2*(M:ℝ)+1) ≤ σ → σ ≤ 5/2 →
      (∀ i : ZeroOccurrence, 1/(C*Real.log (H+4)) ≤ |U-occurrenceOrdinate i|) →
      ‖-deriv riemannZeta ((σ:ℂ)+(U:ℂ)*I) / riemannZeta ((σ:ℂ)+(U:ℂ)*I)‖ ≤
        K*(2*H)^(7/4:ℝ) := by sorry

theorem pairContour_horizontal_tendsto (M : ℕ) (C X t : ℝ)
    (hC : 0 < C) (hX : 1 ≤ X) (U : ℕ → ℝ)
    (hU : ∀ n : ℕ, (n:ℝ)+2 ≤ |U n| ∧ |U n| ≤ (n:ℝ)+3)
    (hgap : ∀ (n : ℕ) (i : ZeroOccurrence),
      1/(C*Real.log ((n:ℝ)+6)) ≤ |U n-occurrenceOrdinate i|) :
    Tendsto (fun n => ∫ σ in -(2*(M:ℝ)+1)..(5/2:ℝ),
      pairContourIntegrand X t ((σ:ℂ)+(U n:ℂ)*I)) atTop (𝓝 0) := by sorry

theorem pairContour_left_integrable (X t : ℝ) (M : ℕ) :
    Integrable (fun v : ℝ => pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I)) := by sorry

theorem pairContour_left_tendsto (X t : ℝ) (hX : 1 < X) :
    Tendsto (fun M : ℕ => ∫ v : ℝ,
      pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I)) atTop (𝓝 0) := by sorry

theorem pairLogWeight_integrable (t : ℝ) :
    Integrable (fun v : ℝ => Real.log (|v|+2)/(1+(v-t)^2)) := by sorry

theorem pairRightIntegral_prime_identity (X t : ℝ) (hX : 1 ≤ X) :
    pairRightIntegral (X,t) + (X:ℂ) *
      (deriv riemannZeta (pairSpectralPoint t+1) / riemannZeta (pairSpectralPoint t+1)) =
      -pairPrimeSeries (X,t) := by sorry

theorem pairTrivialTerm_summable (p : ℝ × ℝ) (hX : 1 ≤ p.1) :
    Summable (fun n => ‖pairTrivialTerm n p‖) := by sorry

theorem pairTrivialCorrection_continuous :
    ContinuousOn pairTrivialCorrection pairSeriesDomain := by sorry

theorem pairTrivialZero_order (n : ℕ) :
    meromorphicOrderAt riemannZeta (-2*(n+1:ℂ)) = (1:ℤ) := by sorry

theorem pairContour_residue_trivial (X t : ℝ) (n : ℕ) :
    residue (pairContourIntegrand X t) (-2*(n+1:ℂ)) = -pairTrivialTerm n (X,t) := by sorry

theorem pairZero_classification (z : ℂ) (hzero : riemannZeta z = 0) :
    (0 < z.re ∧ z.re < 1) ∨ ∃ n : ℕ, z = -2*(n+1:ℂ) := by sorry

end
end HigherCorrelations
