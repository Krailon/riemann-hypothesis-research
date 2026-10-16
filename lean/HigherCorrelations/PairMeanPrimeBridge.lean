import HigherCorrelations.PairMeanValue
import HigherCorrelations.PairMeanPrimeDefinitions
import HigherCorrelations.PairPrimeConvergence

/-! UNCONDITIONAL specialization to the actual explicit-formula prime series.
This does not assert the weighted sieve bound or the prime diagonal asymptotic. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex

theorem pairMeanPrimeCoefficient_nonneg (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    0 ≤ pairMeanPrimeCoefficient X n := by
  unfold pairMeanPrimeCoefficient
  have hv := ArithmeticFunction.vonMangoldt_nonneg (n := n+1)
  have hX0 : 0 < X := by linarith
  positivity

theorem pairMeanPrimeCoefficient_sqrt (X : ℝ) (n : ℕ) :
    pairMeanPrimeCoefficient X n =
      ArithmeticFunction.vonMangoldt (n+1)/Real.sqrt (n+1:ℝ)*min ((n+1:ℝ)/X) (X/(n+1:ℝ)) := by
  have hn : 0 < (n+1:ℝ) := by positivity
  have he : Real.exp (Real.log (n+1:ℝ)*(-(1/2:ℝ))) = (Real.sqrt (n+1:ℝ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn, ← Real.exp_neg]
    congr 1
    ring
  unfold pairMeanPrimeCoefficient
  rw [he]
  simp only [div_eq_mul_inv]

theorem pairMeanPrimeFrequency_injective : Function.Injective pairMeanPrimeFrequency := by
  intro n m h
  have he : Real.log (n+1:ℝ) = Real.log (m+1:ℝ) := by
    unfold pairMeanPrimeFrequency at h
    have := (div_left_inj' (by positivity : (2*Real.pi) ≠ 0)).mp h
    linarith
  have hn : 0 < (n+1:ℝ) := by positivity
  have hm : 0 < (m+1:ℝ) := by positivity
  have hnm := Real.log_injOn_pos hn hm he
  have hnme : (n:ℝ) = m := by linarith
  exact_mod_cast hnme

theorem pairMeanPrimeTerm_frequency (X t : ℝ) (n : ℕ) :
    pairPrimeTerm n (X,t) = (pairMeanPrimeCoefficient X n:ℂ)*
      pairMeanCharacter (pairMeanPrimeFrequency n*t) := by
  have he : (Real.log (n+1:ℝ):ℂ)*(-(1/2:ℂ)-I*t) =
      (Real.log (n+1:ℝ)*(-(1/2:ℝ)):ℂ)+
        2*(Real.pi:ℂ)*I*(pairMeanPrimeFrequency n*t) := by
    unfold pairMeanPrimeFrequency
    push_cast
    field_simp
    ring
  unfold pairPrimeTerm pairMeanPrimeCoefficient pairMeanCharacter
  dsimp only
  rw [he,Complex.exp_add]
  push_cast
  ring

theorem pairMeanPrimeCoefficient_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n => ‖(pairMeanPrimeCoefficient X n:ℂ)‖) := by
  have h := pairPrimeTerm_summable X 0 hX
  simpa only [pairMeanPrimeTerm_frequency,mul_zero,pairMeanCharacter,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,mul_one] using h

theorem pairMeanPrimeSeries_frequency (X t : ℝ) :
    pairPrimeSeries (X,t) = pairFrequencySum pairMeanPrimeFrequency
      (fun n => (pairMeanPrimeCoefficient X n:ℂ)) t := by
  apply tsum_congr
  intro n
  exact pairMeanPrimeTerm_frequency X t n

theorem pairMeanPrimeFrequency_gap (n m : ℕ) :
    |pairMeanPrimeFrequency n-pairMeanPrimeFrequency m| =
      |Real.log ((n+1:ℝ)/(m+1:ℝ))|/(2*Real.pi) := by
  rw [Real.log_div (by positivity : (n+1:ℝ) ≠ 0) (by positivity : (m+1:ℝ) ≠ 0)]
  unfold pairMeanPrimeFrequency
  rw [← sub_div,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  congr 1
  rw [show -Real.log (n+1:ℝ)- -Real.log (m+1:ℝ) =
    -(Real.log (n+1:ℝ)-Real.log (m+1:ℝ)) by ring,abs_neg]

theorem pairMeanPrimeFrequency_cutoff (n m : ℕ) (δ : ℝ) :
    (0 < |pairMeanPrimeFrequency n-pairMeanPrimeFrequency m| ∧
      |pairMeanPrimeFrequency n-pairMeanPrimeFrequency m| < δ) ↔
    (n ≠ m ∧ |Real.log ((n+1:ℝ)/(m+1:ℝ))| < 2*Real.pi*δ) := by
  rw [abs_pos,sub_ne_zero,pairMeanPrimeFrequency_injective.ne_iff,
    pairMeanPrimeFrequency_gap,div_lt_iff₀ (by positivity : 0 < 2*Real.pi),mul_comm δ]

theorem pairMeanPrimeDiagonal_eq (X : ℝ) (hX : 1 ≤ X) :
    pairFrequencyDiagonal (fun n => (pairMeanPrimeCoefficient X n:ℂ)) = pairMeanPrimeDiagonal X := by
  apply tsum_congr
  intro n
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pairMeanPrimeCoefficient_nonneg X hX n)]

theorem pairMeanPrimeNearby_eq (X δ : ℝ) (hX : 1 ≤ X) :
    pairFrequencyNearby pairMeanPrimeFrequency (fun n => (pairMeanPrimeCoefficient X n:ℂ)) δ =
      pairMeanPrimeNearby X δ := by
  apply tsum_congr
  intro p
  simp only [pairMeanPrimeFrequency_cutoff]
  simp only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pairMeanPrimeCoefficient_nonneg X hX p.1),
    abs_of_nonneg (pairMeanPrimeCoefficient_nonneg X hX p.2)]

theorem pairMeanPrime_meanvalue (X T δ : ℝ) (hX : 1 ≤ X)
    (hT : 1 ≤ T) (hδlo : 1/(2*T) ≤ δ) (hδhi : δ ≤ 1/2) :
    |(∫ t in (0:ℝ)..T, ‖pairPrimeSeries (X,t)‖^2)-T*pairMeanPrimeDiagonal X| ≤
      512/δ*pairMeanPrimeDiagonal X+1025*T*pairMeanPrimeNearby X δ := by
  simpa only [← pairMeanPrimeSeries_frequency,pairMeanPrimeDiagonal_eq X hX,
    pairMeanPrimeNearby_eq X δ hX] using pairMeanValue_explicit pairMeanPrimeFrequency
      pairMeanPrimeFrequency_injective (fun n => (pairMeanPrimeCoefficient X n:ℂ))
      (pairMeanPrimeCoefficient_summable X hX) T δ hT hδlo hδhi

end
end HigherCorrelations
