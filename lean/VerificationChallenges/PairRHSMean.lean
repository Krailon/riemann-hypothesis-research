import HigherCorrelations.PairRHSDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! UNCONDITIONAL definition-only statement specifications.
Unfinished challenge proofs are isolated from the solution import graph. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairRHS_log_comparison (T : ℝ) (hT : 3 ≤ T) :
    1 ≤ Real.log T ∧ Real.log T ≤ T ∧
    0 ≤ Real.log (T+2)-Real.log T ∧ Real.log (T+2)-Real.log T ≤ 2/T ∧
    Real.log (T+2) ≤ 2*Real.log T := by sorry

theorem pairRHS_log_square_derivative (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ => (u+2)*(Real.log (u+2)^2-2*Real.log (u+2)+2))
      (Real.log (t+2)^2) t := by sorry

theorem pairRHS_log_square_integral (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, Real.log (t+2)^2) =
      (T+2)*(Real.log (T+2)^2-2*Real.log (T+2)+2)-
      2*(Real.log 2^2-2*Real.log 2+2) := by sorry

theorem pairRHSArch_continuous (X T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (pairRHSArch X) (Set.Icc 0 T) := by sorry

theorem pairRHSArch_square_integral (X T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, ‖pairRHSArch X t‖^2) =
      (1/X^2)*((T+2)*(Real.log (T+2)^2-2*Real.log (T+2)+2)-
        2*(Real.log 2^2-2*Real.log 2+2)) := by sorry

theorem pairRHSArchSquareError_bound (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    |pairRHSArchSquareError X T| ≤ 64*T*Real.log T/X^2 := by sorry

theorem pairRHS_prime_continuous (X : ℝ) (hX : 1 ≤ X) :
    Continuous (fun t : ℝ => pairPrimeSeries (X,t)) := by sorry

theorem pairRHS_remainder_continuous (j : PairRemainderKind) (X : ℝ) (hX : 1 ≤ X) :
    Continuous (pairRHSRemainder j X) := by sorry

theorem pairRHS_remainder_sum (X t : ℝ) :
    pairRHSRemainderSum X t = pairRHSRemainder .arch X t+pairRHSRemainder .ds X t+
      pairRHSRemainder .pole X t+pairRHSRemainder .trivial X t := by sorry

theorem pairRHS_eq_zeroSeries (X t : ℝ) (hX : 1 ≤ X) (ht : 0 ≤ t) :
    pairRHS X t = pairZeroSeries (X,t) := by sorry

theorem pairRHSSquare_integrable (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => ‖pairRHS X t‖^2) MeasureTheory.volume 0 T := by sorry

theorem pairZeroMeanSquare_integrable (X T : ℝ) (hX : 1 ≤ X) :
    IntervalIntegrable (fun t : ℝ => ‖pairZeroSeries (X,t)‖^2) MeasureTheory.volume 0 T := by sorry

theorem pairRHSSquare_eq_zeroMeanSquare (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSSquare X T = pairZeroMeanSquare X T := by sorry

theorem pairRHSPrimeError_cauchy (j : PairRemainderKind) (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    |pairRHSPrimeError j X T| ≤
      2*pairPrimeMeanL2Norm X T*pairRHSL2 (pairRHSRemainder j X) T := by sorry

theorem pairRHSArchError_cauchy (j : PairRemainderKind) (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    |pairRHSArchError j X T| ≤
      2*pairRHSL2 (pairRHSArch X) T*pairRHSL2 (pairRHSRemainder j X) T := by sorry

theorem pairRHSRemainderSquare_bound (K X T : ℝ) (hK : 0 ≤ K) (hX : 1 ≤ X) (hT : 0 ≤ T)
    (hb : ∀ j, pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T) :
    0 ≤ pairRHSRemainderSquare X T ∧ pairRHSRemainderSquare X T ≤ 16*K^2*T := by sorry

theorem pairRHSPrimeError_scale (C K X T : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T)
    (hp : pairPrimeMeanL2Norm X T ≤ C*Real.sqrt (T*Real.log (2*X)))
    (he : ∀ j, pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T) (j : PairRemainderKind) :
    |pairRHSPrimeError j X T| ≤ 4*C*K*(T*Real.sqrt (Real.log T)) := by sorry

theorem pairRHSArchError_small (K X T : ℝ) (j : PairRemainderKind) (hK : 0 ≤ K)
    (hX : 1 ≤ X) (hT : 3 ≤ T)
    (he : pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T/X) :
    |pairRHSArchError j X T| ≤ 4*K*(T*Real.log T/X^2) := by sorry

theorem pairRHSArchError_large (K X T : ℝ) (j : PairRemainderKind) (hK : 0 ≤ K)
    (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T)
    (he : pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt X) :
    |pairRHSArchError j X T| ≤ 4*K*(T*Real.sqrt (Real.log T)) := by sorry

theorem pairRHS_square_algebra (p a h : ℂ) :
    ‖-p+a+h‖^2 = ‖p‖^2+‖a‖^2+‖h‖^2-
      2*(p*star a).re-2*(p*star h).re+2*(a*star h).re := by sorry

theorem pairRHS_integral_re (f : ℝ → ℂ) (T : ℝ)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ t in (0:ℝ)..T, (f t).re) = (∫ t in (0:ℝ)..T, f t).re := by sorry

theorem pairRHS_square_integral (p a h : ℝ → ℂ) (T : ℝ)
    (hp : ContinuousOn p (Set.uIcc 0 T)) (ha : ContinuousOn a (Set.uIcc 0 T))
    (hh : ContinuousOn h (Set.uIcc 0 T)) :
    (∫ t in (0:ℝ)..T, ‖-p t+a t+h t‖^2) =
      (∫ t in (0:ℝ)..T, ‖p t‖^2)+(∫ t in (0:ℝ)..T, ‖a t‖^2)+
      (∫ t in (0:ℝ)..T, ‖h t‖^2)-2*(∫ t in (0:ℝ)..T, p t*star (a t)).re-
      2*(∫ t in (0:ℝ)..T, p t*star (h t)).re+2*(∫ t in (0:ℝ)..T, a t*star (h t)).re := by sorry

theorem pairRHS_cross_sum (f : ℝ → ℂ) (X T : ℝ) (hX : 1 ≤ X)
    (hf : ContinuousOn f (Set.uIcc 0 T)) :
    (∫ t in (0:ℝ)..T, f t*star (pairRHSRemainderSum X t)) =
      ∑ j, ∫ t in (0:ℝ)..T, f t*star (pairRHSRemainder j X t) := by sorry

theorem pairRHS_decomposition (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSSquare X T = T*Real.log T^2/X^2+T*Real.log X+
      pairRHSSmallError X T+pairRHSLargeError X T := by sorry

theorem pairRHSL2_memLp (f : ℝ → ℂ) (T : ℝ)
    (hf : ContinuousOn f (Set.Icc 0 T)) : MemLp f 2 (volume.restrict (Set.Icc 0 T)) := by sorry

theorem pairRHSL2_cauchy (f g : ℝ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Set.Icc 0 T)) (hg : ContinuousOn g (Set.Icc 0 T)) :
    |(∫ t in (0:ℝ)..T, f t*star (g t)).re| ≤ pairRHSL2 f T*pairRHSL2 g T := by sorry

theorem pairRHSL2_square_bound (f : ℝ → ℂ) (T B : ℝ) (hB : 0 ≤ B)
    (hb : (∫ t in (0:ℝ)..T, ‖f t‖^2) ≤ B^2) : pairRHSL2 f T ≤ B := by sorry

theorem pairRHSSmallError_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → |pairRHSSmallError X T| ≤ C*(T*Real.log T/X^2) := by sorry

theorem pairRHSLargeError_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T → |pairRHSLargeError X T| ≤ C*(T*Real.sqrt (Real.log T)) := by sorry

theorem pairRHSMean_uniform : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    pairRHSSquare X T = pairZeroMeanSquare X T ∧
    pairRHSSquare X T = T*Real.log T^2/X^2+T*Real.log X+
      pairRHSSmallError X T+pairRHSLargeError X T ∧
    |pairRHSSmallError X T| ≤ C₁*(T*Real.log T/X^2) ∧
    |pairRHSLargeError X T| ≤ C₂*(T*Real.sqrt (Real.log T)) := by sorry

theorem pairRHSMean_zero_bound : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairZeroMeanSquare X T-(T*Real.log T^2/X^2+T*Real.log X)| ≤
      C*(T*Real.log T/X^2+T*Real.sqrt (Real.log T)) := by sorry

theorem pairRHSMean_unit : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairZeroMeanSquare 1 T-T*Real.log T^2| ≤ C*(T*Real.log T+T*Real.sqrt (Real.log T)) := by sorry

theorem pairRHSMean_top : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
    |pairZeroMeanSquare T T-(T*Real.log T^2/T^2+T*Real.log T)| ≤
      C*(T*Real.log T/T^2+T*Real.sqrt (Real.log T)) := by sorry

theorem pairRHSMean_minimal_height : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → X ≤ 3 →
    |pairZeroMeanSquare X 3-(3*Real.log 3^2/X^2+3*Real.log X)| ≤
      C*(3*Real.log 3/X^2+3*Real.sqrt (Real.log 3)) := by sorry

theorem pairRHS_log_integrals (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => Real.log (t+2)) (Set.uIcc 0 T) ∧
    ContinuousOn (fun t : ℝ => (t+2)⁻¹) (Set.uIcc 0 T) ∧
    (∫ t in (0:ℝ)..T, (t+2)⁻¹) = Real.log (T+2)-Real.log 2 := by sorry

theorem pairRHS_log_oscillation (ω T : ℝ) (hω : 0 < ω) (hT : 0 ≤ T) :
    ‖∫ t in (0:ℝ)..T, (Real.log (t+2):ℂ)*Complex.exp (-Complex.I*ω*t)‖ ≤
      2*Real.log (T+2)/ω := by sorry

theorem pairRHS_integral_tsum {f : ℕ → ℝ → ℂ} (b : ℕ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hf : ∀ n, ContinuousOn (f n) (Set.uIcc 0 T))
    (hbound : ∀ n t, t ∈ Set.Icc 0 T → ‖f n t‖ ≤ b n) :
    (∫ t in (0:ℝ)..T, ∑' n, f n t) = ∑' n, ∫ t in (0:ℝ)..T, f n t := by sorry

theorem pairRHS_primeTerm_phase (X t : ℝ) (n : ℕ) :
    pairPrimeTerm n (X,t) = (pairMeanPrimeCoefficient X n:ℂ)*
      Complex.exp (-Complex.I*(Real.log (n+1:ℝ):ℂ)*t) := by sorry

theorem pairRHS_primeArch_term (X T : ℝ) (n : ℕ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    ‖∫ t in (0:ℝ)..T, pairPrimeTerm n (X,t)*star (pairRHSArch X t)‖ ≤
      (2*Real.log (T+2)/X)*(pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ)) := by sorry

theorem pairRHS_primeArch_interchange (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, pairPrimeSeries (X,t)*star (pairRHSArch X t)) =
      ∑' n : ℕ, ∫ t in (0:ℝ)..T, pairPrimeTerm n (X,t)*star (pairRHSArch X t) := by sorry

theorem pairRHSPrimeArchError_bound (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    |pairRHSPrimeArchError X T| ≤ 20*Real.log (T+2)/Real.sqrt X := by sorry

theorem pairRHS_coefficient_div_log_nonneg (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    0 ≤ pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) := by sorry

theorem pairRHS_coefficient_div_log_bounds (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) ≤ Real.sqrt (n+1:ℝ)/X ∧
    pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ) ≤ X*(n+1:ℝ)^(-3/2:ℝ) := by sorry

theorem pairRHS_coefficient_div_log_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n : ℕ => pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ)) := by sorry

theorem pairRHS_rpow_tail (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ, (n+N+1:ℝ)^(-3/2:ℝ)) ≤ 2/Real.sqrt N := by sorry

theorem pairRHS_coefficient_div_log_sum (X : ℝ) (hX : 1 ≤ X) :
    (∑' n : ℕ, pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ)) ≤ 5*Real.sqrt X := by sorry

theorem pairRHSL2_constant_bound (f : ℝ → ℂ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hf : ContinuousOn f (Set.Icc 0 T)) (hb : ∀ t ∈ Set.Icc 0 T, ‖f t‖ ≤ B) :
    pairRHSL2 f T ≤ B*Real.sqrt T := by sorry

theorem pairRHSL2_decay_bound (f : ℝ → ℂ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hb : ∀ t ∈ Set.Icc 0 T, ‖f t‖^2 ≤ B^2/(1+t^2)) :
    pairRHSL2 f T ≤ 2*B := by sorry

theorem pairRHS_arch_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    pairRHSL2 (pairRHSArch X) T ≤ 2*Real.sqrt T*Real.log T/X := by sorry

theorem pairRHS_archError_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .arch X) T ≤ |pairArchConstant| *Real.sqrt T/X := by sorry

theorem pairRHS_dsError_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .ds X) T ≤ pairDSConstant*Real.sqrt T/X := by sorry

theorem pairRHS_pole_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .pole X) T ≤ 8*Real.sqrt X := by sorry

theorem pairRHS_trivial_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .trivial X) T ≤ 24*X^(-5/2:ℝ) := by sorry

theorem pairRHS_height_scales (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    1 ≤ Real.sqrt T ∧ 1 ≤ Real.sqrt (Real.log T) ∧
    Real.log (2*X) ≤ 2*Real.log T ∧
    Real.sqrt (T*Real.log (2*X)) ≤ 2*Real.sqrt T*Real.sqrt (Real.log T) ∧
    Real.sqrt (T*X*Real.log (2*X)) ≤ 2*T*Real.sqrt (Real.log T) ∧
    Real.sqrt T*Real.log T ≤ T*Real.sqrt (Real.log T) := by sorry

theorem pairRHS_remainder_uniform : ∃ K : ℝ, 0 < K ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    (∀ j, pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T) ∧
    pairRHSL2 (pairRHSRemainder .arch X) T ≤ K*Real.sqrt T/X ∧
    pairRHSL2 (pairRHSRemainder .ds X) T ≤ K*Real.sqrt T/X ∧
    pairRHSL2 (pairRHSRemainder .pole X) T ≤ K*Real.sqrt X ∧
    pairRHSL2 (pairRHSRemainder .trivial X) T ≤ K*Real.sqrt X := by sorry

end
end HigherCorrelations
