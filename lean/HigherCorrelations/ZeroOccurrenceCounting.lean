import HigherCorrelations.ZeroOccurrences
import PrimeNumberTheoremAnd.Backlund.ZeroCountCrude

/-! Inclusive polynomial occurrence counts. Assumptions: UNCONDITIONAL.
The imported ball-mass theorem is used with full analytic multiplicities.
The surrogate/order bridge follows the local proof in ZeroCountCrude.
-/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

private theorem surrogate_divisor_order (ρ : StripZero) :
    (MeromorphicOn.divisor Backlund.zetaSurrogate Set.univ) ρ.val = riemannZeta.order ρ.val := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => w - 1) ρ.val := by fun_prop
  have hmero : MeromorphicOn Backlund.zetaSurrogate Set.univ := fun x _ =>
    (Backlund.zetaSurrogate_differentiable.analyticAt x).meromorphicAt
  have he : Backlund.zetaSurrogate =ᶠ[𝓝 ρ.val] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (stripZero_ne_one ρ)] with w hw
    simp [Backlund.zetaSurrogate, Set.mem_compl_singleton_iff.mp hw]
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ _),
    meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
  change (meromorphicOrderAt ((fun w : ℂ => w - 1) * riemannZeta) ρ.val).untopD 0 = _
  rw [meromorphicOrderAt_mul hlin.meromorphicAt (stripZero_analytic ρ).meromorphicAt]
  have h0 : meromorphicOrderAt (fun w : ℂ => w - 1) ρ.val = 0 := by
    rw [hlin.meromorphicOrderAt_eq]
    have h : analyticOrderAt (fun w : ℂ => w - 1) ρ.val = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr (stripZero_ne_one ρ)))
    simp [h]
  rw [h0, zero_add]
  rfl

theorem occurrenceCutoff_card (U : ℝ) :
    (occurrenceCutoff U).card =
      ∑ ρ ∈ (stripZero_height_finite U).toFinset, zeroMultiplicity ρ := by
  classical
  let : Fintype {ρ : StripZero // |ρ.val.im| ≤ U} := (stripZero_height_finite U).fintype
  let : Fintype {i : ZeroOccurrence // |occurrenceOrdinate i| ≤ U} := (occurrence_height_finite U).fintype
  let := (occurrence_height_finite U).fintype
  have he := Equiv.subtypeSigmaEquiv (fun ρ : StripZero => Fin (zeroMultiplicity ρ))
    (fun ρ => |ρ.val.im| ≤ U)
  have hc := Nat.card_congr he
  rw [Nat.card_sigma] at hc
  simp only [Nat.card_fin] at hc
  have hl : (occurrenceCutoff U).card = Nat.card {i : ZeroOccurrence // |occurrenceOrdinate i| ≤ U} := by
    rw [Nat.card_eq_fintype_card]
    rw [occurrenceCutoff, dite_eq_left (occurrence_height_finite U)]
    exact (occurrence_height_finite U).card_toFinset
  rw [hl]
  change Nat.card {i : ZeroOccurrence // |i.1.val.im| ≤ U} = _
  rw [hc]
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x _
    exact (stripZero_height_finite U).mem_toFinset.mpr x.property
  · intro x _ y _ h
    exact Subtype.ext h
  · intro ρ hρ
    exact ⟨⟨ρ, (stripZero_height_finite U).mem_toFinset.mp hρ⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

theorem occurrenceCutoff_le_mass (U : ℝ) (hU : 0 ≤ U) :
    ((occurrenceCutoff U).card : ℝ) ≤
      Complex.Hadamard.divisorMassClosedBall₀ Backlund.zetaSurrogate (U + 1) := by
  classical
  rw [occurrenceCutoff_card, Nat.cast_sum]
  set D := MeromorphicOn.divisor Backlund.zetaSurrogate Set.univ
  set S := (stripZero_height_finite U).toFinset
  have hDnn : 0 ≤ D := Differentiable.divisor_nonneg Backlund.zetaSurrogate_differentiable
  have he : (∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ)) =
      ∑ z ∈ S.image (fun ρ => ρ.val), (D z : ℝ) := by
    rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext hab)]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [show D ρ.val = riemannZeta.order ρ.val from surrogate_divisor_order ρ,
      ← zeroMultiplicity_order]
    norm_cast
  rw [he, Complex.Hadamard.divisorMassClosedBall₀,
    Function.locallyFinsuppWithin.massClosedBall₀]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
    have hord : D ρ.val ≠ 0 := by
      rw [surrogate_divisor_order, ← zeroMultiplicity_order]
      exact_mod_cast (zeroMultiplicity_pos ρ).ne'
    have hb : ‖ρ.val‖ ≤ |U + 1| := by
      rw [abs_of_nonneg (by linarith)]
      have hheight : |ρ.val.im| ≤ U := (stripZero_height_finite U).mem_toFinset.mp hρ
      calc
        ‖ρ.val‖ ≤ |ρ.val.re| + |ρ.val.im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ U + 1 := by rw [abs_of_pos ρ.property.2.1]; linarith [ρ.property.2.2]
    have hm := Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
      (Function.mem_support.mpr hord) hb
    refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hm, ?_⟩
    intro hz0
    have := ρ.property.2.1
    simp [hz0] at this
  · intro z _ _
    exact_mod_cast hDnn z

theorem occurrence_count_polynomial :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 ≤ U →
      ((occurrenceCutoff U).card : ℝ) ≤ C * (1 + U) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := Backlund.zetaSurrogate_zeros_in_closedBall₀_count
  refine ⟨4 * C, by positivity, fun U hU => ?_⟩
  have hb := (occurrenceCutoff_le_mass U hU).trans (hbound (U + 1) (by linarith))
  have hp : (1 + (U + 1)) ^ (3 / 2 : ℝ) ≤ (1 + (U + 1)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  calc
    _ ≤ C * (1 + (U + 1)) ^ 2 := hb.trans (mul_le_mul_of_nonneg_left hp hC.le)
    _ ≤ (4 * C) * (1 + U) ^ 2 := by nlinarith [sq_nonneg U]

end
end HigherCorrelations
