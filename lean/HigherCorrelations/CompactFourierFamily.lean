import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-! Uniform Fourier decay for compact smooth families. UNCONDITIONAL.
The parameter remains in a compact set; no uniformity over unbounded parameters is asserted.
-/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem section_fderiv_smooth {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → V → G) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × V => fderiv ℝ (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞ (Function.uncurry (fun p : E × V => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hFp.fderiv contDiff_snd (by simp)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem section_iteratedFDeriv_smooth (F : E → V → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : E × V => iteratedFDeriv ℝ n (F p.1) p.2) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ V ℂ).symm.toContinuousLinearEquiv.contDiff.comp hF
  | succ n ih =>
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).symm.toContinuousLinearEquiv.contDiff.comp
      (section_fderiv_smooth (fun y => iteratedFDeriv ℝ n (F y)) ih)

theorem compact_family_derivative_integral_bound (F : E → V → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set V) (hK : IsCompact K)
    (hsupp : ∀ y, Function.support (F y) ⊆ K) (J : Set E) (hJ : IsCompact J) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ J, (∫ v, ‖iteratedFDeriv ℝ n (F y) v‖) ≤ C := by
  have hc := (section_iteratedFDeriv_smooth F hF n).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  refine ⟨(|M| + 1) * (volume.real K + 1), by positivity, ?_⟩
  intro y hy
  have hb : ∀ v ∈ K, ‖iteratedFDeriv ℝ n (F y) v‖ ≤ |M| + 1 := by
    intro v hv
    exact (hM (Set.mem_image_of_mem _ (show (y, v) ∈ J ×ˢ K from ⟨hy, hv⟩))).trans
      (by linarith [le_abs_self M])
  have hz : ∀ v, v ∉ K → ‖iteratedFDeriv ℝ n (F y) v‖ = 0 := by
    intro v hv
    have hs : Function.support (iteratedFDeriv ℝ n (F y)) ⊆ K :=
      (subset_tsupport _).trans ((tsupport_iteratedFDeriv_subset n).trans
        (closure_minimal (hsupp y) hK.isClosed))
    have he : iteratedFDeriv ℝ n (F y) v = 0 := by by_contra hn; exact hv (hs hn)
    simp [he]
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun v => ‖iteratedFDeriv ℝ n (F y) v‖) hK.measure_lt_top
    (C := |M| + 1) (fun v hv => by simpa using hb v hv)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    Real.norm_of_nonneg (integral_nonneg (fun v => norm_nonneg _))] at hi
  exact hi.trans (by nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : E → V → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set V) (hK : IsCompact K)
    (hsupp : ∀ y, Function.support (F y) ⊆ K) (J : Set E) (hJ : IsCompact J) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ J, ∀ x : V, ‖x‖ ^ n * ‖𝓕 (F y) x‖ ≤ C := by
  choose c hc hb using fun j : ℕ => compact_family_derivative_integral_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ n * (∑ j ∈ Finset.range (n + 1), c j) + 1, ?_, ?_⟩
  · have hh : 0 ≤ ∑ j ∈ Finset.range (n + 1), c j := Finset.sum_nonneg (fun j _ => (hc j).le)
    positivity
  · intro y hy x
    have hs : ContDiff ℝ ∞ (F y) := hF.comp (contDiff_const.prodMk contDiff_id)
    have hcompact : HasCompactSupport (F y) := HasCompactSupport.of_support_subset_isCompact hK (hsupp y)
    let f := hcompact.toSchwartzMap hs
    have hi (k j : ℕ) (_hk : (k : ℕ∞) ≤ 0) (_hj : (j : ℕ∞) ≤ n) :
        Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ j (F y) v‖) :=
      SchwartzMap.integrable_pow_mul_iteratedFDeriv volume f k j
    have hh := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := (0 : ℕ∞)) (N := (n : ℕ∞))
      (hs.of_le (by simp)) hi (k := 0) (n := n) le_rfl le_rfl x
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, mul_zero, zero_add,
      Finset.range_one, Finset.singleton_product, Finset.sum_map, Function.Embedding.sectR_apply, Nat.cast_zero] at hh
    apply hh.trans
    calc
      _ ≤ 2 ^ n * (∑ j ∈ Finset.range (n + 1), c j) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Finset.sum_le_sum
        intro j hj
        exact hb j y hy
      _ ≤ _ := by linarith

theorem compact_family_fourier_decay (F : E → V → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set V) (hK : IsCompact K)
    (hsupp : ∀ y, Function.support (F y) ⊆ K) (J : Set E) (hJ : IsCompact J) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ J, ∀ x : V, ‖𝓕 (F y) x‖ ≤ C / (1 + ‖x‖) ^ n := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cn, hCn, hn⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ n
  refine ⟨2 ^ n * (C₀ + Cn), by positivity, ?_⟩
  intro y hy x
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖) ^ n)).mpr
  have hb : ‖𝓕 (F y) x‖ ≤ C₀ := by simpa using h0 y hy x
  have hp := hn y hy x
  rw [mul_comm]
  by_cases hx : ‖x‖ ≤ 1
  · calc
      _ ≤ 2 ^ n * ‖𝓕 (F y) x‖ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) n) (norm_nonneg _)
      _ ≤ 2 ^ n * (C₀ + Cn) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hpow : (1 + ‖x‖) ^ n ≤ (2 * ‖x‖) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      _ ≤ (2 * ‖x‖) ^ n * ‖𝓕 (F y) x‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = 2 ^ n * (‖x‖ ^ n * ‖𝓕 (F y) x‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ n * (C₀ + Cn) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end
end HigherCorrelations
