import HigherCorrelations.TripleBudgetDefinitions
import HigherCorrelations.TripleMasterAssembly

/-! UNCONDITIONAL exact accounting. These identities alone assert no decay. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudgetWeight_support (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    Function.support ω ⊆ Icc (1:ℝ) 2 :=
  fun _ hu => Ioo_subset_Icc_self (hω.support (subset_tsupport ω hu))

theorem tripleBudgetMoment_scale (ω : ℝ → ℝ) (T : ℝ) (hT : 0<T) (r : ℕ) :
    (∫ t : ℝ, ω (t/T)/T * Real.log (|t|+2)^r) = tripleBudgetMoment ω T r := by
  have he : (fun t : ℝ => ω (t/T)/T * Real.log (|t|+2)^r) =
      fun t => (ω (t/T)*Real.log (|T*(t/T)|+2)^r)/T := by
    funext t
    rw [mul_div_cancel₀ t hT.ne']
    ring
  rw [he,integral_div]
  rw [Measure.integral_comp_div (fun u => ω u*Real.log (|T*u|+2)^r) T,abs_of_pos hT,smul_eq_mul]
  exact mul_div_cancel_left₀ _ hT.ne'

theorem tripleBudgetMoment_manuscript (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤T) (r : ℕ) :
    tripleBudgetMoment ω T r = ∫ u in Ioo (1:ℝ) 2, ω u*Real.log (T*u+2)^r := by
  unfold tripleBudgetMoment
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Ioo (1:ℝ) 2
  · rw [indicator_of_mem hu,abs_of_nonneg (mul_nonneg hT (by linarith [hu.1]))]
  · have hz : ω u = 0 := by
      by_contra hn
      exact hu (hω.support (subset_tsupport ω hn))
    simp [hu,hz]

theorem tripleBudget_AAA (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T) :
    tripleWordIntegral ω T X Y ![.A,.A,.A] =
      (tripleBudgetMoment ω T 3/(X*Y)^2 : ℝ) := by
  have he : tripleWordIntegrand ω T X Y ![.A,.A,.A] =
      fun t => (((ω (t/T)/T * Real.log (|t|+2)^3)/(X*Y)^2 : ℝ) : ℂ) := by
    funext t
    simp [tripleWordIntegrand,tripleSmoothedIntegrand,tripleComponent,tripleArch]
    push_cast
    ring
  rw [tripleWordIntegral,he,integral_complex_ofReal,integral_div,
    tripleBudgetMoment_scale ω T hT 3]

theorem tripleBudget_remainder_count : tripleBudgetRemainderWords.card = 19 := by decide

theorem tripleBudget_refinement_count :
    (∑ w ∈ tripleBudgetRemainderWords, Fintype.card (TripleBudgetAssignment w)) = 208 := by decide

theorem tripleBudget_exact (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y = tripleBudgetRetained ω T X Y +
      (∑ e : TripleBudgetError, tripleBudgetError ω T X Y e) +
      ∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w := by
  rw [tripleMaster_word_split ω hω hs T X Y hT hX hY]
  congr 1
  have hf : Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = false) =
      {![.P,.P,.P],![.P,.P,.A],![.P,.A,.P],![.P,.A,.A],
       ![.A,.P,.P],![.A,.P,.A],![.A,.A,.P],![.A,.A,.A]} := by decide
  rw [hf]
  simp only [tripleWordSign,tripleWordPrimeCount,Fin.sum_univ_three]
  simp [show (Finset.univ : Finset TripleBudgetError) =
      {.archcube,.PPA,.PAA,.APA,.AAP,.PAPoff,.APPoff,.PPPoff} from rfl,
    tripleBudgetError,tripleBudgetRetained,tripleBudget_AAA ω T X Y (by linarith)]
  push_cast
  ring

theorem tripleBudget_PPPoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleBudgetError ω T X Y .PPPoff = -triplePrimeOffSeries ω T X Y := by
  have hm : (∫ u : ℝ, (ω u:ℂ)) = 1 := by
    rw [integral_complex_ofReal,hω.mass,Complex.ofReal_one]
  have he := triplePrime_resonance_unit_mass ω hω.smooth.continuous
    (tripleBudgetWeight_support ω hω) hm T X Y hT hX hY
  dsimp [tripleBudgetError]
  rw [he]
  ring

end
end HigherCorrelations
