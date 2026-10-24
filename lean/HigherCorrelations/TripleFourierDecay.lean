import HigherCorrelations.PairMeanFourierDecay
import HigherCorrelations.TriplePrimeResonance

/-! UNCONDITIONAL cubic-frequency decay in the exact project convention.
Only individual off-resonant summands are bounded; no summed smallness follows. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

/-- The positive integer arguments make log(mn/k)=0 equivalent to mn=k. -/
theorem triplePrimeFrequency_eq_zero (T : ℝ) (hT : 0<T) (v : PrimeTriple) :
    triplePrimeFrequency T v = 0 ↔ triplePrimeResonant v := by
  constructor
  · intro he
    have hn : T/(2*Real.pi) ≠ 0 := div_ne_zero hT.ne' (by positivity)
    have hl : Real.log (((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ)/((v 2+1:ℕ):ℝ)) = 0 :=
      (mul_eq_zero.mp he).resolve_left hn
    have hh := Real.eq_one_of_pos_of_log_eq_zero (by positivity) hl
    have hh' := (div_eq_one_iff_eq (by positivity : ((v 2+1:ℕ):ℝ)≠0)).mp hh
    unfold triplePrimeResonant
    exact_mod_cast hh'
  · intro hv
    exact triplePrimeFrequency_resonance T v hv

theorem triplePrimeFrequency_ne_zero (T : ℝ) (hT : 0<T) (v : PrimeTriple) :
    triplePrimeFrequency T v ≠ 0 ↔ ¬triplePrimeResonant v :=
  not_congr (triplePrimeFrequency_eq_zero T hT v)

theorem triplePrimeFrequency_decay_scale (T : ℝ) (hT : 0<T) (v : PrimeTriple) :
    2*Real.pi*|triplePrimeFrequency T v| =
      T*|Real.log (((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ)/((v 2+1:ℕ):ℝ))| := by
  unfold triplePrimeFrequency
  rw [abs_mul,abs_div,abs_of_pos hT,abs_of_pos (by positivity : 0<2*Real.pi)]
  field_simp

/-- Closed smoothing support suffices; all derivatives are globally defined. -/
theorem tripleWeight_fourier_decay (ω : ℝ → ℝ) (N : ℕ) (hω : ContDiff ℝ N ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (ξ : ℝ) (hξ : ξ≠0) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤
      min (fourierDerivativeL1 ω 0) (fourierDerivativeL1 ω N/(2*Real.pi*|ξ|)^N) :=
  fourierDecay_real_min ω N hω
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs) ξ hξ

theorem tripleWeight_fourier_smooth (ω : ℝ → ℝ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (N : ℕ) (ξ : ℝ) (hξ : ξ≠0) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) ξ‖ ≤
      min (fourierDerivativeL1 ω 0) (fourierDerivativeL1 ω N/(2*Real.pi*|ξ|)^N) :=
  tripleWeight_fourier_decay ω N (hω.of_le (by simp)) hs ξ hξ

theorem tripleWeight_cubic_decay (ω : ℝ → ℝ) (N : ℕ) (hω : ContDiff ℝ N ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T)
    (v : PrimeTriple) (hv : ¬triplePrimeResonant v) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) (triplePrimeFrequency T v)‖ ≤
      min (fourierDerivativeL1 ω 0)
        (fourierDerivativeL1 ω N/(T*|Real.log (((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ)/((v 2+1:ℕ):ℝ))|)^N) := by
  have h := tripleWeight_fourier_decay ω N hω hs (triplePrimeFrequency T v)
    ((triplePrimeFrequency_ne_zero T hT v).mpr hv)
  rwa [triplePrimeFrequency_decay_scale T hT v] at h

theorem triplePrimeFourierTerm_norm_factor (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) :
    ‖triplePrimeFourierTerm ω T X Y v‖ = triplePrimeCoefficient X Y v*
      ‖pairMeanFourier (fun u => (ω u:ℂ)) (triplePrimeFrequency T v)‖ := by
  simp only [triplePrimeFourierTerm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (triplePrimeCoefficient_nonneg X Y hX hY v)]

theorem triplePrimeFourierTerm_mass_bound (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) :
    ‖triplePrimeFourierTerm ω T X Y v‖ ≤ triplePrimeCoefficient X Y v*fourierDerivativeL1 ω 0 := by
  rw [triplePrimeFourierTerm_norm_factor ω T X Y hX hY v]
  exact mul_le_mul_of_nonneg_left (fourierDecay_real_mass ω _)
    (triplePrimeCoefficient_nonneg X Y hX hY v)

theorem triplePrimeFourierTerm_decay (ω : ℝ → ℝ) (N : ℕ) (hω : ContDiff ℝ N ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) (hv : ¬triplePrimeResonant v) :
    ‖triplePrimeFourierTerm ω T X Y v‖ ≤ triplePrimeCoefficient X Y v*
      min (fourierDerivativeL1 ω 0)
        (fourierDerivativeL1 ω N/(T*|Real.log (((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ)/((v 2+1:ℕ):ℝ))|)^N) := by
  rw [triplePrimeFourierTerm_norm_factor ω T X Y hX hY v]
  exact mul_le_mul_of_nonneg_left (tripleWeight_cubic_decay ω N hω hs T (by linarith) v hv)
    (triplePrimeCoefficient_nonneg X Y hX hY v)

theorem tripleWeight_cubic_uniform (ω : ℝ → ℝ) (N : ℕ) (hω : ContDiff ℝ N ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (D₀ Dₙ : ℝ)
    (h0 : fourierDerivativeL1 ω 0 ≤ D₀) (hn : fourierDerivativeL1 ω N ≤ Dₙ)
    (T : ℝ) (hT : 0<T) (v : PrimeTriple) (hv : ¬triplePrimeResonant v) :
    ‖pairMeanFourier (fun u => (ω u:ℂ)) (triplePrimeFrequency T v)‖ ≤
      min D₀ (Dₙ/(T*|Real.log (((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ)/((v 2+1:ℕ):ℝ))|)^N) := by
  have h := fourierDecay_real_uniform ω N hω
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs) D₀ Dₙ h0 hn
    (triplePrimeFrequency T v) ((triplePrimeFrequency_ne_zero T hT v).mpr hv)
  rwa [triplePrimeFrequency_decay_scale T hT v] at h

theorem triplePrimeFourierTerm_decay_minimal (ω : ℝ → ℝ) (N : ℕ) (hω : ContDiff ℝ N ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (v : PrimeTriple) (hv : ¬triplePrimeResonant v) :
    ‖triplePrimeFourierTerm ω 3 1 1 v‖ ≤ triplePrimeCoefficient 1 1 v*
      min (fourierDerivativeL1 ω 0)
        (fourierDerivativeL1 ω N/(3*|Real.log (((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ)/((v 2+1:ℕ):ℝ))|)^N) :=
  triplePrimeFourierTerm_decay ω N hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num) v hv

end
end HigherCorrelations
