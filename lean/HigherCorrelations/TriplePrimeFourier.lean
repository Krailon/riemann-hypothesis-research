import HigherCorrelations.TriplePrimeFourierDefinitions
import HigherCorrelations.TripleExpansion
import HigherCorrelations.PairMeanFourierRules

/-! UNCONDITIONAL cubic prime product, absolute integral-norm summability and
Fourier identification. T,X,Y,omega are fixed before the three cutoffs are removed. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

private def primeTripleEquiv : PrimeTriple ≃ (ℕ × ℕ) × ℕ where
  toFun v := ((v 0,v 1),v 2)
  invFun q := ![q.1.1,q.1.2,q.2]
  left_inv v := by funext r; fin_cases r <;> rfl
  right_inv q := rfl

private theorem coefficient_summable (X : ℝ) (hX : 1≤X) :
    Summable (pairMeanPrimeCoefficient X) := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pairMeanPrimeCoefficient_nonneg X hX _)] using
    pairMeanPrimeCoefficient_summable X hX

private theorem xy_ge_one (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) : 1≤X*Y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]

theorem triplePrimeCoefficient_nonneg (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) :
    0 ≤ triplePrimeCoefficient X Y v :=
  mul_nonneg (mul_nonneg (pairMeanPrimeCoefficient_nonneg X hX _)
    (pairMeanPrimeCoefficient_nonneg Y hY _))
    (pairMeanPrimeCoefficient_nonneg (X*Y) (xy_ge_one X Y hX hY) _)

theorem triplePrimeCoefficient_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (triplePrimeCoefficient X Y) := by
  have hp := (coefficient_summable X hX).mul_of_nonneg (coefficient_summable Y hY)
    (pairMeanPrimeCoefficient_nonneg X hX) (pairMeanPrimeCoefficient_nonneg Y hY)
  have hq := hp.mul_of_nonneg (coefficient_summable (X*Y) (xy_ge_one X Y hX hY))
    (fun q => mul_nonneg (pairMeanPrimeCoefficient_nonneg X hX q.1)
      (pairMeanPrimeCoefficient_nonneg Y hY q.2))
    (pairMeanPrimeCoefficient_nonneg (X*Y) (xy_ge_one X Y hX hY))
  have hi : Function.Injective (fun v : PrimeTriple => ((v 0,v 1),v 2)) := by
    intro v w h
    funext r
    fin_cases r
    · exact congrArg (fun q => q.1.1) h
    · exact congrArg (fun q => q.1.2) h
    · exact congrArg (fun q => q.2) h
  change Summable ((fun q : (ℕ × ℕ) × ℕ =>
    pairMeanPrimeCoefficient X q.1.1 * pairMeanPrimeCoefficient Y q.1.2 *
      pairMeanPrimeCoefficient (X*Y) q.2) ∘ (fun v : PrimeTriple => ((v 0,v 1),v 2)))
  exact hq.comp_injective hi

theorem triplePrimeCoefficient_mass (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' v : PrimeTriple, triplePrimeCoefficient X Y v) =
      triplePrimeMass X*triplePrimeMass Y*triplePrimeMass (X*Y) := by
  have hp := (coefficient_summable X hX).mul_of_nonneg (coefficient_summable Y hY)
    (pairMeanPrimeCoefficient_nonneg X hX) (pairMeanPrimeCoefficient_nonneg Y hY)
  have hq := hp.mul_of_nonneg (coefficient_summable (X*Y) (xy_ge_one X Y hX hY))
    (fun q => mul_nonneg (pairMeanPrimeCoefficient_nonneg X hX q.1)
      (pairMeanPrimeCoefficient_nonneg Y hY q.2))
    (pairMeanPrimeCoefficient_nonneg (X*Y) (xy_ge_one X Y hX hY))
  have hh := (((coefficient_summable X hX).hasSum.mul (coefficient_summable Y hY).hasSum hp).mul
    (coefficient_summable (X*Y) (xy_ge_one X Y hX hY)).hasSum hq).tsum_eq
  rw [← primeTripleEquiv.symm.tsum_eq (triplePrimeCoefficient X Y)]
  have h0 (q : (ℕ × ℕ) × ℕ) : primeTripleEquiv.symm q 0 = q.1.1 := rfl
  have h1 (q : (ℕ × ℕ) × ℕ) : primeTripleEquiv.symm q 1 = q.1.2 := rfl
  have h2 (q : (ℕ × ℕ) × ℕ) : primeTripleEquiv.symm q 2 = q.2 := rfl
  simpa only [triplePrimeCoefficient,h0,h1,h2,triplePrimeMass] using hh

theorem triplePrimeFrequency_phase (T : ℝ) (v : PrimeTriple) :
    triplePrimeFrequency T v =
      T*(-pairMeanPrimeFrequency (v 0)-pairMeanPrimeFrequency (v 1)+pairMeanPrimeFrequency (v 2)) := by
  unfold triplePrimeFrequency pairMeanPrimeFrequency
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

/-- The conjugated third slot gives log(mn/k) with the positive Fourier argument. -/
theorem triplePrimeTerm_phase (ω : ℝ → ℝ) (T X Y : ℝ) (v : PrimeTriple) (t : ℝ) :
    triplePrimeTerm ω T X Y v t = (triplePrimeCoefficient X Y v:ℂ)*
      ((ω (t/T)/T:ℝ)*pairMeanCharacter (-t*triplePrimeFrequency 1 v)) := by
  simp only [triplePrimeTerm,pairMeanPrimeTerm_frequency,star_mul,
    Complex.star_def,Complex.conj_ofReal,pairMeanCharacter_conj]
  have he : (pairMeanPrimeFrequency (v 0)*t+pairMeanPrimeFrequency (v 1)*t)+
      -(pairMeanPrimeFrequency (v 2)*t) = -t*triplePrimeFrequency 1 v := by
    rw [triplePrimeFrequency_phase]
    ring
  rw [← he,pairMeanCharacter_add,pairMeanCharacter_add]
  unfold triplePrimeCoefficient
  push_cast
  ring

theorem triplePrimeTerm_norm (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T)
    (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) (t : ℝ) :
    ‖triplePrimeTerm ω T X Y v t‖ = triplePrimeCoefficient X Y v*(|ω (t/T)|/T) := by
  rw [triplePrimeTerm_phase]
  simp only [norm_mul,pairMeanCharacter_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (triplePrimeCoefficient_nonneg X Y hX hY v),abs_div,abs_of_pos hT]

theorem triplePrimeTerm_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ) (hT : 0<T)
    (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) : Integrable (triplePrimeTerm ω T X Y v) := by
  have hc : Continuous (triplePrimeTerm ω T X Y v) := by
    rw [show triplePrimeTerm ω T X Y v = fun t => (triplePrimeCoefficient X Y v:ℂ)*
      ((ω (t/T)/T:ℝ)*pairMeanCharacter (-t*triplePrimeFrequency 1 v)) from
        funext (triplePrimeTerm_phase ω T X Y v)]
    exact continuous_const.mul ((Complex.continuous_ofReal.comp
      ((hω.comp (continuous_id.div_const T)).div_const T)).mul
        (pairMeanCharacter_continuous.comp (by fun_prop)))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply tripleMaster_support ω hs T hT
  intro hz
  exact ht (by simp [triplePrimeTerm,hz])

theorem triplePrimeTerm_integralNorm (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T)
    (hX : 1≤X) (hY : 1≤Y) (v : PrimeTriple) :
    (∫ t : ℝ, ‖triplePrimeTerm ω T X Y v t‖) =
      triplePrimeCoefficient X Y v*(∫ u : ℝ, |ω u|) := by
  simp_rw [triplePrimeTerm_norm ω T X Y hT hX hY v]
  rw [integral_const_mul,tripleMaster_weight_mass ω T hT]

/-- A T-independent bound, in fact an equality for the sum of integral norms. -/
theorem triplePrime_integralNorm (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T)
    (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : PrimeTriple => ∫ t : ℝ, ‖triplePrimeTerm ω T X Y v t‖) ∧
    (∑' v : PrimeTriple, ∫ t : ℝ, ‖triplePrimeTerm ω T X Y v t‖) = triplePrimeL1Bound ω X Y := by
  simp_rw [triplePrimeTerm_integralNorm ω T X Y hT hX hY]
  refine ⟨(triplePrimeCoefficient_summable X Y hX hY).mul_right _, ?_⟩
  rw [tsum_mul_right,triplePrimeCoefficient_mass X Y hX hY]
  rfl

theorem triplePrime_pointwise_summable (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T)
    (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    Summable (fun v : PrimeTriple => ‖triplePrimeTerm ω T X Y v t‖) := by
  simp_rw [triplePrimeTerm_norm ω T X Y hT hX hY]
  exact (triplePrimeCoefficient_summable X Y hX hY).mul_right _

theorem triplePrimeTerm_fourier (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T) (v : PrimeTriple) :
    (∫ t : ℝ, triplePrimeTerm ω T X Y v t) = triplePrimeFourierTerm ω T X Y v := by
  simp_rw [triplePrimeTerm_phase]
  rw [integral_const_mul]
  unfold triplePrimeFourierTerm
  congr 1
  have he : (fun t : ℝ => (ω (t/T)/T:ℝ)*pairMeanCharacter (-t*triplePrimeFrequency 1 v)) =
      fun t => (1/(T:ℂ))*(pairMeanCharacter (-t*triplePrimeFrequency 1 v)*(ω (t/T):ℂ)) := by
    funext t
    push_cast
    ring
  rw [he,integral_const_mul]
  change (1/(T:ℂ))*pairMeanFourier (fun t => (ω (t/T):ℂ)) (triplePrimeFrequency 1 v) = _
  rw [pairMeanFourier_div (fun u => (ω u:ℂ)) T _ hT.ne',abs_of_pos hT]
  have hf : T*triplePrimeFrequency 1 v = triplePrimeFrequency T v := by
    rw [triplePrimeFrequency_phase,triplePrimeFrequency_phase]
    ring
  rw [hf]
  have hTc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp [hTc]

theorem triplePrime_finite_product (ω : ℝ → ℝ) (T X Y t : ℝ)
    (S : Fin 3 → Finset ℕ) :
    (∑ v ∈ tripleDomain S, triplePrimeTerm ω T X Y v t) =
      (ω (t/T)/T : ℝ)*(∑ i ∈ S 0, pairPrimeTerm i (X,t))*
        (∑ j ∈ S 1, pairPrimeTerm j (Y,t))*
        star (∑ k ∈ S 2, pairPrimeTerm k (X*Y,t)) := by
  classical
  let f : Fin 3 → ℕ → ℂ :=
    ![fun i => pairPrimeTerm i (X,t), fun i => pairPrimeTerm i (Y,t),
      fun i => star (pairPrimeTerm i (X*Y,t))]
  have hp := Finset.prod_univ_sum S f
  simp only [Fin.prod_univ_three] at hp
  have ht (v : PrimeTriple) : triplePrimeTerm ω T X Y v t =
      (ω (t/T)/T : ℝ)*(f 0 (v 0)*f 1 (v 1)*f 2 (v 2)) := by
    simp [triplePrimeTerm, f, mul_assoc]
  simp_rw [ht]
  rw [← Finset.mul_sum, tripleDomain, ← hp]
  simp [f, mul_assoc]

/-- The infinite product is identified by absolutely convergent finite products. -/
theorem triplePrime_product_eq (ω : ℝ → ℝ)
    (T X Y : ℝ) (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    (∑' v : PrimeTriple, triplePrimeTerm ω T X Y v t) =
      tripleWordIntegrand ω T X Y ![.P,.P,.P] t := by
  classical
  have hXY : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hlim := occurrence_cutoff_limit atTop
    (fun S : Finset ℕ => tripleDomain (fun _ : Fin 3 => S))
    (fun v => eventually_atTop.mpr ⟨Finset.univ.image v, fun S hS => by
      rw [tripleDomain, Fintype.mem_piFinset]
      exact fun r => hS (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩)
    (fun v => triplePrimeTerm ω T X Y v t)
    (triplePrime_pointwise_summable ω T X Y hT hX hY t)
  have hx := (pairPrimeTerm_summable X t hX).of_norm.hasSum
  have hy := (pairPrimeTerm_summable Y t hY).of_norm.hasSum
  have hz := (pairPrimeTerm_summable (X*Y) t hXY).of_norm.hasSum
  have hp := (((tendsto_const_nhds (x := ((ω (t/T)/T : ℝ) : ℂ))).mul hx).mul hy).mul
    (show Tendsto (fun S : Finset ℕ => star (∑ k ∈ S, pairPrimeTerm k (X*Y,t)))
      atTop (𝓝 (star (∑' k, pairPrimeTerm k (X*Y,t)))) from
      continuous_star.continuousAt.tendsto.comp hz)
  simp_rw [triplePrime_finite_product] at hlim
  exact tendsto_nhds_unique hlim hp

/-- Absolute convergence of the evaluated Fourier series. -/
theorem triplePrimeFourier_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : PrimeTriple => ‖triplePrimeFourierTerm ω T X Y v‖) := by
  have ht : 0<T := by linarith
  have h := evaluated_integrals_summable volume (triplePrimeTerm ω T X Y)
    (triplePrimeTerm_integrable ω hω hs T X Y ht hX hY) _
    (triplePrime_integralNorm ω T X Y ht hX hY).1
    (fun v => norm_integral_le_integral_norm _)
  simpa only [triplePrimeTerm_fourier ω T X Y ht] using h

theorem triplePrimeFourier_norm_bound (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    (∑' v : PrimeTriple, ‖triplePrimeFourierTerm ω T X Y v‖) ≤ triplePrimeL1Bound ω X Y := by
  have ht : 0<T := by linarith
  calc
    _ ≤ ∑' v : PrimeTriple, ∫ t : ℝ, ‖triplePrimeTerm ω T X Y v t‖ :=
      (triplePrimeFourier_summable ω hω hs T X Y hT hX hY).tsum_le_tsum
        (fun v => by rw [← triplePrimeTerm_fourier ω T X Y ht]; exact norm_integral_le_integral_norm _)
        (triplePrime_integralNorm ω T X Y ht hX hY).1
    _ = _ := (triplePrime_integralNorm ω T X Y ht hX hY).2

theorem triplePrime_sum_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    (∑' v : PrimeTriple, ∫ t : ℝ, triplePrimeTerm ω T X Y v t) =
      ∫ t : ℝ, ∑' v : PrimeTriple, triplePrimeTerm ω T X Y v t :=
  integral_occurrence_sum volume (triplePrimeTerm ω T X Y)
    (triplePrimeTerm_integrable ω hω hs T X Y (by linarith) hX hY)
    (triplePrime_integralNorm ω T X Y (by linarith) hX hY).1

/-- Unsigned cubic prime identity, in cycles and with the literal T/(2 pi). -/
theorem triplePrime_fourier_identity (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleWordIntegral ω T X Y ![.P,.P,.P] =
      ∑' v : PrimeTriple, triplePrimeFourierTerm ω T X Y v := by
  unfold tripleWordIntegral
  simp_rw [← triplePrime_product_eq ω T X Y (by linarith) hX hY]
  rw [← triplePrime_sum_integral ω hω hs T X Y hT hX hY]
  simp_rw [triplePrimeTerm_fourier ω T X Y (by linarith)]

/-- The cubic term appears with a minus sign in the 27-word expansion. -/
theorem triplePrime_signed_PPP (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    (tripleWordSign ![.P,.P,.P]:ℂ)*tripleWordIntegral ω T X Y ![.P,.P,.P] =
      -(∑' v : PrimeTriple, triplePrimeFourierTerm ω T X Y v) := by
  rw [triplePrime_fourier_identity ω hω hs T X Y hT hX hY]
  have hsign : tripleWordSign ![.P,.P,.P] = -1 := by decide
  rw [hsign]
  simp

theorem triplePrimeFourier_finite_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun S : Fin 3 → Finset ℕ =>
      ∑ v ∈ tripleDomain S, triplePrimeFourierTerm ω T X Y v) atTop
      (𝓝 (tripleWordIntegral ω T X Y ![.P,.P,.P])) := by
  rw [triplePrime_fourier_identity ω hω hs T X Y hT hX hY]
  exact triple_cutoff_limit _ (triplePrimeFourier_summable ω hω hs T X Y hT hX hY)

/-- range N corresponds to positive integers 1 through N, including N in full. -/
theorem triplePrimeFourier_integer_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun N : Fin 3 → ℕ =>
      ∑ v ∈ tripleDomain (fun r => Finset.range (N r)), triplePrimeFourierTerm ω T X Y v) atTop
      (𝓝 (tripleWordIntegral ω T X Y ![.P,.P,.P])) := by
  rw [triplePrime_fourier_identity ω hω hs T X Y hT hX hY]
  apply independent_sequence_cutoff_limit (fun _ => Finset.range) _ _
    (triplePrimeFourier_summable ω hω hs T X Y hT hX hY)
  intro r i
  exact eventually_atTop.mpr ⟨i+1,fun n hn => Finset.mem_range.mpr (by omega)⟩

theorem triplePrime_finite_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (S : Fin 3 → Finset ℕ) :
    (∫ t : ℝ, (ω (t/T)/T:ℝ)*(∑ n ∈ S 0, pairPrimeTerm n (X,t))*
      (∑ n ∈ S 1, pairPrimeTerm n (Y,t))*star (∑ n ∈ S 2, pairPrimeTerm n (X*Y,t))) =
      ∑ v ∈ tripleDomain S, triplePrimeFourierTerm ω T X Y v := by
  simp_rw [← triplePrime_finite_product]
  rw [integral_finsetSum _ (fun v _ => triplePrimeTerm_integrable ω hω hs T X Y (by linarith) hX hY v)]
  simp_rw [triplePrimeTerm_fourier ω T X Y (by linarith)]

theorem triplePrime_integral_finite_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun S : Fin 3 → Finset ℕ =>
      ∫ t : ℝ, (ω (t/T)/T:ℝ)*(∑ n ∈ S 0, pairPrimeTerm n (X,t))*
        (∑ n ∈ S 1, pairPrimeTerm n (Y,t))*star (∑ n ∈ S 2, pairPrimeTerm n (X*Y,t))) atTop
      (𝓝 (tripleWordIntegral ω T X Y ![.P,.P,.P])) := by
  simpa only [triplePrime_finite_integral ω hω hs T X Y hT hX hY] using
    triplePrimeFourier_finite_cutoff ω hω hs T X Y hT hX hY

theorem triplePrime_integral_integer_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun N : Fin 3 → ℕ =>
      ∫ t : ℝ, (ω (t/T)/T:ℝ)*(∑ n ∈ Finset.range (N 0), pairPrimeTerm n (X,t))*
        (∑ n ∈ Finset.range (N 1), pairPrimeTerm n (Y,t))*
        star (∑ n ∈ Finset.range (N 2), pairPrimeTerm n (X*Y,t))) atTop
      (𝓝 (tripleWordIntegral ω T X Y ![.P,.P,.P])) := by
  have he (N : Fin 3 → ℕ) := triplePrime_finite_integral ω hω hs T X Y hT hX hY
    (fun r => Finset.range (N r))
  simp_rw [he]
  exact triplePrimeFourier_integer_cutoff ω hω hs T X Y hT hX hY

theorem triplePrimeFrequency_resonance (T : ℝ) (v : PrimeTriple)
    (hv : (v 0+1)*(v 1+1) = v 2+1) : triplePrimeFrequency T v = 0 := by
  unfold triplePrimeFrequency
  have he : ((v 0+1:ℕ):ℝ)*((v 1+1:ℕ):ℝ) = ((v 2+1:ℕ):ℝ) := by exact_mod_cast hv
  rw [he,div_self (by positivity),Real.log_one,mul_zero]

/-- A resonant term retains integral omega; unit mass is not a hidden premise. -/
theorem triplePrimeFourier_resonance (ω : ℝ → ℝ) (T X Y : ℝ) (v : PrimeTriple)
    (hv : (v 0+1)*(v 1+1) = v 2+1) :
    triplePrimeFourierTerm ω T X Y v =
      (triplePrimeCoefficient X Y v:ℂ)*(∫ u : ℝ, (ω u:ℂ)) := by
  rw [triplePrimeFourierTerm,triplePrimeFrequency_resonance T v hv,pairMeanFourier_zero]

theorem triplePrimeFourier_integer_one (ω : ℝ → ℝ) (T X Y : ℝ) (v : PrimeTriple)
    (r : Fin 3) (hr : v r = 0) : triplePrimeFourierTerm ω T X Y v = 0 := by
  fin_cases r <;> simp_all [triplePrimeFourierTerm,triplePrimeCoefficient,pairMeanPrimeCoefficient]

theorem triplePrime_fourier_minimal (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    tripleWordIntegral ω 3 1 1 ![.P,.P,.P] =
      ∑' v : PrimeTriple, triplePrimeFourierTerm ω 3 1 1 v :=
  triplePrime_fourier_identity ω hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num)

theorem triplePrimeFourier_zero_weight (T X Y : ℝ) (v : PrimeTriple) :
    triplePrimeFourierTerm (fun _ => 0) T X Y v = 0 := by
  simp [triplePrimeFourierTerm,pairMeanFourier]

theorem triplePrimeFourier_neg_weight (ω : ℝ → ℝ) (T X Y : ℝ) (v : PrimeTriple) :
    triplePrimeFourierTerm (fun t => -ω t) T X Y v = -triplePrimeFourierTerm ω T X Y v := by
  simp [triplePrimeFourierTerm,pairMeanFourier,integral_neg]

end
end HigherCorrelations
