import HigherCorrelations.TripleMasterStatement
import HigherCorrelations.TripleFourierDecay

/-! UNCONDITIONAL assembly of the exact smoothed triple master formula.
One existential zero-kernel constant is chosen before all weights and parameters.
Its historical numerical effectiveness is not asserted here. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleMasterProduct_swap (ω : ℝ → ℝ) (T X Y t : ℝ) :
    tripleMasterProduct ω T X Y t = tripleMasterProduct ω T Y X t := by
  unfold tripleMasterProduct
  rw [mul_comm Y X]
  ring

theorem tripleMasterObservable_swap (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterObservable ω T X Y = tripleMasterObservable ω T Y X := by
  unfold tripleMasterObservable
  simp_rw [tripleMasterProduct_swap ω T X Y]

theorem tripleMasterObservable_integral_series (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y = ∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω T X Y v t := by
  rw [tripleMaster_sum_integral ω hω hs T X Y hT hX hY]
  unfold tripleMasterObservable
  simp_rw [tripleMaster_product_eq ω hs T X Y hT hX hY]

theorem tripleMasterObservable_norm_bound (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : Continuous ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleMasterObservable ω T X Y‖ ≤ tripleMasterL1Bound C₀ ω T X Y := by
  have hi := tripleMaster_integralNorm_bound C₀ hC₀ hQ ω hω hs T X Y hT hX hY
  have he := tripleMaster_evaluated_norm_summable ω hω hs T X Y hT hX hY
  rw [tripleMasterObservable_integral_series ω hω hs T X Y hT hX hY]
  calc
    _ ≤ ∑' v : MasterTriple, ‖∫ t : ℝ, tripleMasterTerm ω T X Y v t‖ := norm_tsum_le_tsum_norm he
    _ ≤ ∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖ :=
      he.tsum_le_tsum (fun v => norm_integral_le_integral_norm _) hi.1
    _ ≤ _ := hi.2

/-- Assembly for an explicitly supplied zero-kernel constant. -/
theorem tripleMaster_assembled (C₀ : ℝ) (hC₀ : 0<C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) : TripleMasterStatement C₀ ω T X Y := by
  have hc := hω.continuous
  have hi := tripleMaster_integralNorm_bound C₀ hC₀.le hQ ω hc hs T X Y hT hX hY
  exact {
    integral_norm_summable := hi.1
    integral_norm_bound := hi.2
    sum_integral := tripleMaster_sum_integral ω hc hs T X Y hT hX hY
    kernel_absolute := tripleMaster_kernel_norm_summable ω hc hs T X Y hT hX hY
    kernel_identity := tripleMaster_kernel_identity ω hc hs T X Y hT hX hY
    pattern_absolute := tripleMasterPattern_norm_summable ω hc hs T X Y hT hX hY
    pattern_decomposition := tripleMaster_pattern_decomposition ω hc hs T X Y hT hX hY
    five_subseries := tripleMaster_five_subseries ω hc hs T X Y hT hX hY
    symmetry := tripleMasterObservable_swap ω T X Y
    observable_bound := tripleMasterObservable_norm_bound C₀ hC₀.le hQ ω hc hs T X Y hT hX hY
    word_expansion := tripleMaster_word_expansion ω hc hs T X Y hT hX hY
    word_table := tripleMaster_table_expansion ω hc hs T X Y hT hX hY
    word_count := tripleWord_counts.1
    prime_absolute := triplePrimeFourier_summable ω hc hs T X Y hT hX hY
    prime_identity := triplePrime_fourier_identity ω hc hs T X Y hT hX hY
    resonant_absolute := triplePrime_resonant_norm_summable ω hc hs T X Y hT hX hY
    off_absolute := triplePrime_off_norm_summable ω hc hs T X Y hT hX hY
    resonance_classification := triplePrimeResonance_nonzero X Y hX hY
    resonance_mass_absolute := triplePrimeResonantMass_norm_summable X Y hX hY
    resonance_nested := triplePrimeResonantMass_nested X Y hX hY
    resonance_value := triplePrime_resonant_series ω T X Y hX hY
    prime_split := triplePrime_resonance_split ω hc hs T X Y hT hX hY
    signed_PPP := triplePrime_resonance_signed ω hc hs T X Y hT hX hY
    fourier_mass := fourierDecay_real_mass ω
    fourier_decay := fun N ξ hξ => fourierDecay_real_bound ω N (hω.of_le (by simp))
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs) ξ hξ }

/-- C₀ is chosen once, before every smoothing weight, height and pair of bases. -/
theorem tripleMaster_uniform : ∃ C₀ : ℝ, 0<C₀ ∧
    (∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2)) ∧
    ∀ (ω : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T X Y : ℝ, 3≤T → 1≤X → 1≤Y → TripleMasterStatement C₀ ω T X Y := by
  obtain ⟨C,hC,hQ,_⟩ := tripleMaster_uniform_integralNorm
  exact ⟨C,hC,hQ,fun ω hω hs T X Y hT hX hY =>
    tripleMaster_assembled C hC hQ ω hω hs T X Y hT hX hY⟩

theorem tripleMaster_weight_mass_one (ω : ℝ → ℝ) (hn : ∀ u, 0≤ω u)
    (hm : ∫ u : ℝ, ω u = 1) :
    fourierDerivativeL1 ω 0 = 1 ∧ (∫ u : ℝ, (ω u:ℂ)) = 1 := by
  constructor
  · rw [fourierDerivativeL1_zero_order]
    simpa only [abs_of_nonneg (hn _)] using hm
  · rw [integral_complex_ofReal,hm,Complex.ofReal_one]

/-- The manuscript's stronger support and probability assumptions specialize the signed theorem. -/
theorem tripleMaster_manuscript (C₀ : ℝ) (hC₀ : 0<C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : tsupport ω ⊆ Ioo (1:ℝ) 2)
    (hn : ∀ u, 0≤ω u) (hm : ∫ u : ℝ, ω u = 1)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    TripleMasterStatement C₀ ω T X Y ∧ fourierDerivativeL1 ω 0 = 1 ∧
    (∫ u : ℝ, (ω u:ℂ)) = 1 ∧
    ‖tripleMasterObservable ω T X Y‖ ≤ (8/3:ℝ)^3*C₀^3*X*Y*Real.log (2*T+2)^3 ∧
    tripleWordIntegral ω T X Y ![.P,.P,.P] = (triplePrimeResonantMass X Y:ℂ)+triplePrimeOffSeries ω T X Y ∧
    (tripleWordSign ![.P,.P,.P]:ℂ)*tripleWordIntegral ω T X Y ![.P,.P,.P] =
      -(triplePrimeResonantMass X Y:ℂ)-triplePrimeOffSeries ω T X Y := by
  have hs' : Function.support ω ⊆ Icc (1:ℝ) 2 := (subset_tsupport ω).trans (hs.trans Ioo_subset_Icc_self)
  have h := tripleMaster_assembled C₀ hC₀ hQ ω hω hs' T X Y hT hX hY
  have hw := tripleMaster_weight_mass_one ω hn hm
  refine ⟨h,hw.1,hw.2,?_,?_,?_⟩
  · have hb := h.observable_bound
    simpa only [tripleMasterL1Bound,← fourierDerivativeL1_zero_order,hw.1,mul_one] using hb
  · simpa only [hw.2,one_mul] using h.prime_split
  · simpa only [hw.2,neg_one_mul] using h.signed_PPP

theorem tripleMasterObservable_neg (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterObservable (fun t => -ω t) T X Y = -tripleMasterObservable ω T X Y := by
  simp only [tripleMasterObservable,tripleMasterProduct,neg_div,Complex.ofReal_neg,neg_mul,integral_neg]

theorem tripleMasterL1Bound_neg (C₀ : ℝ) (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterL1Bound C₀ (fun t => -ω t) T X Y = tripleMasterL1Bound C₀ ω T X Y := by
  simp [tripleMasterL1Bound]

theorem tripleMaster_assembled_minimal (C₀ : ℝ) (hC₀ : 0<C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) : TripleMasterStatement C₀ ω 3 1 1 :=
  tripleMaster_assembled C₀ hC₀ hQ ω hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num)

theorem tripleMaster_assembled_zero (C₀ : ℝ) (hC₀ : 0<C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    TripleMasterStatement C₀ (fun _ => 0) T X Y ∧
    tripleMasterObservable (fun _ => 0) T X Y = 0 ∧
    tripleMasterL1Bound C₀ (fun _ => 0) T X Y = 0 := by
  refine ⟨tripleMaster_assembled C₀ hC₀ hQ _ contDiff_const (by simp) T X Y hT hX hY,?_,?_⟩
  · simp [tripleMasterObservable,tripleMasterProduct]
  · simp [tripleMasterL1Bound]

theorem tripleMaster_assembled_neg (C₀ : ℝ) (hC₀ : 0<C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    TripleMasterStatement C₀ (fun t => -ω t) T X Y ∧
    ‖tripleMasterObservable (fun t => -ω t) T X Y‖ ≤ tripleMasterL1Bound C₀ ω T X Y := by
  have hs' : Function.support (fun t => -ω t) ⊆ Icc (1:ℝ) 2 := by simpa using hs
  have h := tripleMaster_assembled C₀ hC₀ hQ _ hω.neg hs' T X Y hT hX hY
  exact ⟨h,by simpa only [tripleMasterL1Bound_neg] using h.observable_bound⟩

theorem tripleMaster_assembled_swapped (C₀ : ℝ) (hC₀ : 0<C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    TripleMasterStatement C₀ ω T Y X ∧ tripleMasterObservable ω T X Y = tripleMasterObservable ω T Y X :=
  ⟨tripleMaster_assembled C₀ hC₀ hQ ω hω hs T Y X hT hY hX,tripleMasterObservable_swap ω T X Y⟩

end
end HigherCorrelations
