import HigherCorrelations.PairPrimeMeanDefinitions

/-! UNCONDITIONAL independent statement specifications. Deliberately unfinished
challenge proofs are isolated from all solution imports. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairPrimeMean_combined_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairPrimeMeanSquare X T-T*Real.log X| ≤ C*(T+Real.sqrt (T*X*Real.log (2*X))) := by sorry

theorem pairPrimeMean_uniform : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairPrimeMeanOffdiag X T| ≤ C*Real.sqrt (T*X*Real.log (2*X)) ∧
    |pairPrimeMeanDiagonalError X T| ≤ C*T ∧
    pairPrimeMeanL2Norm X T ≤ C*Real.sqrt (T*Real.log (2*X)) := by sorry

theorem pairPrimeMean_unit : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairPrimeMeanOffdiag 1 T| ≤ C*Real.sqrt (T*Real.log 2) ∧
    |pairPrimeMeanDiagonalError 1 T| ≤ C*T := by sorry

theorem pairPrimeMean_top : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairPrimeMeanOffdiag T T| ≤ C*Real.sqrt (T*T*Real.log (2*T)) ∧
    |pairPrimeMeanDiagonalError T T| ≤ C*T := by sorry

theorem pairPrimeMean_minimal_height : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → X ≤ 3 →
    |pairPrimeMeanOffdiag X 3| ≤ C*Real.sqrt (3*X*Real.log (2*X)) ∧
    |pairPrimeMeanDiagonalError X 3| ≤ C*3 := by sorry

theorem pairPrimeMean_log_bounds (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    0 < Real.log (2*X) ∧ Real.log (2*X) ≤ X ∧ X ≤ T*Real.log (2*X) := by sorry

theorem pairPrimeMeanBandwidth_pos (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    0 < pairPrimeMeanBandwidth X T := by sorry

theorem pairPrimeMeanBandwidth_admissible (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    1/(2*T) ≤ pairPrimeMeanBandwidth X T ∧ pairPrimeMeanBandwidth X T ≤ 1/2 := by sorry

theorem pairPrimeMeanBandwidth_balance (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    Real.log (2*X)/pairPrimeMeanBandwidth X T = 2*Real.sqrt (T*X*Real.log (2*X)) ∧
    T*pairPrimeMeanBandwidth X T*X = Real.sqrt (T*X*Real.log (2*X))/2 := by sorry

theorem pairPrimeMeanSquare_integrable (X T : ℝ) (hX : 1 ≤ X) :
    IntervalIntegrable (fun t : ℝ => ‖pairPrimeSeries (X,t)‖^2) volume 0 T := by sorry

theorem pairPrimeMeanSquare_nonneg (X T : ℝ) (hT : 0 ≤ T) : 0 ≤ pairPrimeMeanSquare X T := by sorry

theorem pairPrimeMean_decomposition (X T : ℝ) :
    pairPrimeMeanSquare X T = T*pairMeanPrimeDiagonal X+pairPrimeMeanOffdiag X T ∧
    T*pairMeanPrimeDiagonal X = T*Real.log X+pairPrimeMeanDiagonalError X T ∧
    pairPrimeMeanSquare X T = T*Real.log X+pairPrimeMeanDiagonalError X T+pairPrimeMeanOffdiag X T := by sorry

theorem pairPrimeMeanOffdiag_of_bounds (A B X T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T)
    (hD : pairMeanPrimeDiagonal X ≤ A*Real.log (2*X))
    (hQ : pairMeanPrimeNearby X (pairPrimeMeanBandwidth X T) ≤ B*pairPrimeMeanBandwidth X T*X) :
    |pairPrimeMeanOffdiag X T| ≤ (1024*A+1025*B/2)*Real.sqrt (T*X*Real.log (2*X)) := by sorry

theorem pairPrimeMeanOffdiag_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairPrimeMeanOffdiag X T| ≤ C*Real.sqrt (T*X*Real.log (2*X)) := by sorry

theorem pairPrimeMeanDiagonalError_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 0 ≤ T → |pairPrimeMeanDiagonalError X T| ≤ C*T := by sorry

theorem pairPrimeMean_error_scale (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    Real.sqrt (T*X*Real.log (2*X)) ≤ 2*(T*Real.log (2*X)) := by sorry

theorem pairPrimeMeanSquare_upper : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → pairPrimeMeanSquare X T ≤ C*(T*Real.log (2*X)) := by sorry

theorem pairPrimeMeanL2Norm_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → pairPrimeMeanL2Norm X T ≤ C*Real.sqrt (T*Real.log (2*X)) := by sorry
end
end HigherCorrelations
