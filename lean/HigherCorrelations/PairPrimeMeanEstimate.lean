import HigherCorrelations.PairPrimeMeanBandwidth
import HigherCorrelations.PairDiagonalEndpoints
import HigherCorrelations.PairSieveEndpoints

/-! UNCONDITIONAL. Optimized error for the actual prime series.
The final constants are existential and independent of X and T. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairPrimeMeanSquare_integrable (X T : ℝ) (hX : 1 ≤ X) :
    IntervalIntegrable (fun t : ℝ => ‖pairPrimeSeries (X,t)‖^2) volume 0 T := by
  have hc := pairFrequencySum_continuous pairMeanPrimeFrequency
    (fun n => (pairMeanPrimeCoefficient X n:ℂ)) (pairMeanPrimeCoefficient_summable X hX)
  convert (hc.norm.pow 2).intervalIntegrable (μ := volume) 0 T using 1
  funext t
  simp only [Pi.pow_apply, pairMeanPrimeSeries_frequency]

theorem pairPrimeMeanSquare_nonneg (X T : ℝ) (hT : 0 ≤ T) : 0 ≤ pairPrimeMeanSquare X T :=
  intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg _)

theorem pairPrimeMean_decomposition (X T : ℝ) :
    pairPrimeMeanSquare X T = T*pairMeanPrimeDiagonal X+pairPrimeMeanOffdiag X T ∧
    T*pairMeanPrimeDiagonal X = T*Real.log X+pairPrimeMeanDiagonalError X T ∧
    pairPrimeMeanSquare X T = T*Real.log X+pairPrimeMeanDiagonalError X T+pairPrimeMeanOffdiag X T := by
  unfold pairPrimeMeanOffdiag pairPrimeMeanDiagonalError
  constructor
  · ring
  constructor <;> ring

/-- The numerical coefficient is explicit relative to the diagonal and sieve constants. -/
theorem pairPrimeMeanOffdiag_of_bounds (A B X T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T)
    (hD : pairMeanPrimeDiagonal X ≤ A*Real.log (2*X))
    (hQ : pairMeanPrimeNearby X (pairPrimeMeanBandwidth X T) ≤ B*pairPrimeMeanBandwidth X T*X) :
    |pairPrimeMeanOffdiag X T| ≤ (1024*A+1025*B/2)*Real.sqrt (T*X*Real.log (2*X)) := by
  have hd := pairPrimeMeanBandwidth_pos X T hX hT
  obtain ⟨hdlo,hdhi⟩ := pairPrimeMeanBandwidth_admissible X T hX hT hXT
  obtain ⟨hb1,hb2⟩ := pairPrimeMeanBandwidth_balance X T hX hT
  have hm := pairMeanPrime_meanvalue X T (pairPrimeMeanBandwidth X T) hX (by linarith) hdlo hdhi
  change |pairPrimeMeanOffdiag X T| ≤ _ at hm
  apply hm.trans
  calc
    _ ≤ 512/pairPrimeMeanBandwidth X T*(A*Real.log (2*X))+
        1025*T*(B*pairPrimeMeanBandwidth X T*X) :=
      add_le_add (mul_le_mul_of_nonneg_left hD (by positivity))
        (mul_le_mul_of_nonneg_left hQ (by linarith))
    _ = 512*A*(Real.log (2*X)/pairPrimeMeanBandwidth X T)+
        1025*B*(T*pairPrimeMeanBandwidth X T*X) := by ring
    _ = _ := by rw [hb1,hb2]; ring

theorem pairPrimeMeanOffdiag_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairPrimeMeanOffdiag X T| ≤ C*Real.sqrt (T*X*Real.log (2*X)) := by
  obtain ⟨A,hA,ha⟩ := pairMeanPrimeDiagonal_upper
  have hB := pairSieveNearbyConstant_pos
  refine ⟨1024*A+1025*pairSieveNearbyConstant/2, by positivity, ?_⟩
  intro X T hX hT hXT
  have hd := pairPrimeMeanBandwidth_pos X T hX hT
  have hhi := (pairPrimeMeanBandwidth_admissible X T hX hT hXT).2
  exact pairPrimeMeanOffdiag_of_bounds A pairSieveNearbyConstant X T hA.le hB.le hX hT hXT
    (ha X hX) (pairMeanPrimeNearby_bound X _ hX hd.le hhi)

theorem pairPrimeMeanDiagonalError_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 0 ≤ T → |pairPrimeMeanDiagonalError X T| ≤ C*T := by
  obtain ⟨C,hC,hb⟩ := pairMeanPrimeDiagonal_asymptotic
  refine ⟨C,hC,?_⟩
  intro X T hX hT
  unfold pairPrimeMeanDiagonalError
  rw [← mul_sub,abs_mul,abs_of_nonneg hT]
  simpa only [mul_comm C T] using mul_le_mul_of_nonneg_left (hb X hX) hT

theorem pairPrimeMean_error_scale (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    Real.sqrt (T*X*Real.log (2*X)) ≤ 2*(T*Real.log (2*X)) := by
  have hT0 : 0 < T := by linarith
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl : (1/2:ℝ) ≤ Real.log (2*X) := hl2.trans (Real.log_le_log (by norm_num) (by linarith))
  apply (Real.sqrt_le_left (by positivity)).mpr
  calc
    _ ≤ T*T*Real.log (2*X) := by gcongr
    _ ≤ (T*T*Real.log (2*X))*(4*Real.log (2*X)) := by
      have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 4*Real.log (2*X) by linarith)
        (show 0 ≤ T*T*Real.log (2*X) by positivity)
      simpa using this
    _ = _ := by ring

theorem pairPrimeMeanSquare_upper : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → pairPrimeMeanSquare X T ≤ C*(T*Real.log (2*X)) := by
  obtain ⟨A,hA,ha⟩ := pairMeanPrimeDiagonal_upper
  obtain ⟨B,hB,hb⟩ := pairPrimeMeanOffdiag_bound
  refine ⟨A+2*B, by positivity, ?_⟩
  intro X T hX hT hXT
  have hd := mul_le_mul_of_nonneg_left (ha X hX) (show 0 ≤ T by linarith)
  have he := (le_abs_self _).trans (hb X T hX hT hXT)
  have hs := mul_le_mul_of_nonneg_left (pairPrimeMean_error_scale X T hX hT hXT) hB.le
  have hi := (pairPrimeMean_decomposition X T).1
  nlinarith

theorem pairPrimeMeanL2Norm_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → pairPrimeMeanL2Norm X T ≤ C*Real.sqrt (T*Real.log (2*X)) := by
  obtain ⟨A,hA,ha⟩ := pairPrimeMeanSquare_upper
  refine ⟨Real.sqrt A, Real.sqrt_pos.mpr hA, ?_⟩
  intro X T hX hT hXT
  have he := Real.sqrt_le_sqrt (ha X T hX hT hXT)
  rwa [Real.sqrt_mul hA.le] at he

end
end HigherCorrelations
