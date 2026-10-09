import HigherCorrelations.OccurrenceSummability
import HigherCorrelations.OccurrenceIntegration

/-! UNCONDITIONAL exact examples. These are abstract occurrence families,
not synthetic locations or assertions about actual zeta zeros.
-/
namespace HigherCorrelations
open Filter MeasureTheory
open scoped Topology

theorem geometric_tail_example (N : ℕ) :
    (∑' n : ℕ, if N ≤ n then (1 / 2 : ℝ) ^ n else 0) =
      2 * (1 / 2 : ℝ) ^ N := by
  rw [geometric_tail_eq]
  simp_rw [pow_add]
  rw [(summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).tsum_mul_right]
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

theorem repeated_labels_tsum_example (z : ℂ) :
    (∑' _i : Fin 2, z) = (2 : ℂ) * z := by
  have h := tsum_regroup_finite_fibers (fun _ : Fin 2 => ())
    (fun _ : Unit => Finset.univ) (by simp) (fun _ => z) (hasSum_fintype _).summable
  simpa only [tsum_fintype, Fintype.sum_unique, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] using h

theorem empty_occurrence_tsum_example (f : Empty → ℂ) : (∑' i, f i) = 0 := by simp

theorem reflection_fixed_point_tsum_example (f : (Fin 3 → ℕ) → ℂ)
    (hf : Summable (fun t => ‖f t‖)) (e : Fin 3 → Bool) :
    (∑' t, f (reflectSlots id e t)) = ∑' t, f t :=
  tsum_reflectSlots id (fun _ => rfl) e f hf

theorem independent_cutoff_example (f : (Fin 3 → ℕ) → ℂ)
    (hf : Summable (fun t => ‖f t‖)) :
    Tendsto (fun N : Fin 3 → ℕ =>
      ∑ t ∈ tripleDomain (fun j => Finset.range (N j + j.val)), f t)
      atTop (𝓝 (∑' t, f t)) := by
  apply independent_sequence_cutoff_limit (fun j n => Finset.range (n + j.val)) ?_ f hf
  intro j i
  filter_upwards [eventually_gt_atTop i] with n hn
  simp only [Finset.mem_range]
  omega

theorem integrated_empty_example {I : Type*} (δ : I → ℝ) (b : ℝ)
    (φ : ℝ × ℝ → ℝ) : integratedCoshExcess ∅ δ b φ = 0 := by
  simp [integratedCoshExcess, sameOrdinateCoshSum]

theorem integrated_zero_scale_example {I : Type*} (D : Finset I) (δ : I → ℝ)
    (φ : ℝ × ℝ → ℝ) : integratedCoshExcess D δ 0 φ = 0 := by
  simp [integratedCoshExcess, sameOrdinateCoshSum, horizontalCoshExcess]

theorem integrated_zero_weight_example {I : Type*} (D : Finset I) (δ : I → ℝ)
    (b : ℝ) : integratedCoshExcess D δ b (fun _ => 0) = 0 ∧
      integratedFrequencyForm (fun _ => 0) = 0 := by
  simp [integratedCoshExcess, integratedFrequencyForm]

theorem moving_singleton_summable (n : ℕ) : Summable (movingSingleton n) :=
  (hasSum_ite_eq n (1 : ℝ)).summable

theorem moving_singleton_sum (n : ℕ) : (∑' i, movingSingleton n i) = 1 := by
  simp [movingSingleton]

theorem moving_singleton_pointwise (i : ℕ) :
    Tendsto (fun n => movingSingleton n i) atTop (𝓝 0) := by
  apply Filter.EventuallyEq.tendsto
  filter_upwards [eventually_gt_atTop i] with n hn
  simp [movingSingleton, ne_of_lt hn]

theorem moving_singleton_no_majorant (B : ℕ → ℝ) (hB : Summable B)
    (hbound : ∀ n i, ‖movingSingleton n i‖ ≤ B i) : False := by
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) := by
    apply hB.of_nonneg_of_le (fun _ => by norm_num)
    intro i
    simpa [movingSingleton] using hbound i i
  exact (by norm_num : (1 : ℝ) ≠ 0) ((summable_const_iff (1 : ℝ)).mp hs)

theorem moving_singleton_limit_mismatch :
    Tendsto (fun n => ∑' i, movingSingleton n i) atTop (𝓝 1) ∧
    (∑' _i : ℕ, (0 : ℝ)) ≠ 1 := by
  simp only [moving_singleton_sum, tsum_zero]
  exact ⟨tendsto_const_nhds, by norm_num⟩

theorem singleton_shell_summable_example :
    Summable (fun n : ℕ => ‖(1 / 2 : ℂ) ^ n‖) := by
  let S : OccurrenceShells ℕ :=
    { shell := id
      members := fun n => {n}
      mem_iff := by intro i n; simp }
  apply dyadic_summable_norm S _ 1 1 (by norm_num) (by norm_num) 0 1 (by omega)
  · intro n; simp [S]
  · intro n
    simp [S, norm_pow]

theorem dyadic_endpoint_example (d : ℕ) :
    dyadicRatio d d = 1 ∧ ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  constructor
  · simp [dyadicRatio]
  · simp [summable_const_iff]

end HigherCorrelations
