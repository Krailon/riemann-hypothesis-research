import HigherCorrelations.ZeroOccurrenceDefinitions
import HigherCorrelations.ZeroReflection
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting

/-! Actual occurrence foundations. Assumptions: UNCONDITIONAL.
Only finite positive analytic orders are used to form multiplicity fibers.
-/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

def stripZeroToKadiri (ρ : StripZero) : Kadiri.NontrivialZeros :=
  ⟨ρ.val, ⟨ρ.property.2, Set.mem_univ _, ρ.property.1⟩⟩

theorem stripZero_ne_one (ρ : StripZero) : ρ.val ≠ 1 :=
  Kadiri.nontrivialZero_ne_one (stripZeroToKadiri ρ)

theorem stripZero_analytic (ρ : StripZero) : AnalyticAt ℂ riemannZeta ρ.val :=
  Kadiri.riemannZeta_analyticAt_nontrivialZero (stripZeroToKadiri ρ)

theorem stripZero_order_finite (ρ : StripZero) : analyticOrderAt riemannZeta ρ.val ≠ ⊤ := by
  intro h
  have hm := Kadiri.riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero (stripZeroToKadiri ρ)
  apply hm
  change meromorphicOrderAt riemannZeta ρ.val = ⊤
  rw [(stripZero_analytic ρ).meromorphicOrderAt_eq, h]
  rfl

theorem zeroMultiplicity_order (ρ : StripZero) :
    (zeroMultiplicity ρ : ℤ) = riemannZeta.order ρ.val := by
  rw [riemannZeta.order, (stripZero_analytic ρ).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (stripZero_order_finite ρ)]
  rfl

theorem zeroMultiplicity_pos (ρ : StripZero) : 0 < zeroMultiplicity ρ := by
  have h := Kadiri.riemannZeta_order_pos_nontrivialZero (stripZeroToKadiri ρ)
  change 0 < riemannZeta.order ρ.val at h
  rw [← zeroMultiplicity_order] at h
  exact_mod_cast h

theorem zeroMultiplicity_conjugate (ρ : StripZero) :
    zeroMultiplicity (stripZeroConjugate ρ) = zeroMultiplicity ρ := by
  apply Int.natCast_inj.mp
  rw [zeroMultiplicity_order, zeroMultiplicity_order]
  exact Kadiri.riemannZeta_order_conj (stripZero_ne_one ρ)

theorem stripZero_height_finite (U : ℝ) :
    Set.Finite {ρ : StripZero | |ρ.val.im| ≤ U} := by
  have h := Kadiri.nontrivialZeros_abs_im_lt_finite (U + 1)
  have hinj : Function.Injective stripZeroToKadiri := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : Kadiri.NontrivialZeros => (x : ℂ)) hab)
  apply (h.preimage hinj.injOn).subset
  intro ρ hρ
  change |ρ.val.im| < U + 1
  change |ρ.val.im| ≤ U at hρ
  linarith

theorem occurrence_height_finite (U : ℝ) :
    Set.Finite {i : ZeroOccurrence | |occurrenceOrdinate i| ≤ U} := by
  have h := stripZero_height_finite U
  have : Finite {ρ : StripZero // |ρ.val.im| ≤ U} := h.to_subtype
  let f : ((ρ : {ρ : StripZero // |ρ.val.im| ≤ U}) × Fin (zeroMultiplicity ρ.val)) →
      ZeroOccurrence := fun i => ⟨i.1.val, i.2⟩
  apply (Set.toFinite (Set.range f)).subset
  intro i hi
  exact ⟨⟨⟨i.1, hi⟩, i.2⟩, rfl⟩

@[simp] theorem mem_occurrenceCutoff (i : ZeroOccurrence) (U : ℝ) :
    i ∈ occurrenceCutoff U ↔ |occurrenceOrdinate i| ≤ U := by
  classical
  simp [occurrenceCutoff, occurrence_height_finite U]

theorem occurrenceCutoff_negative (U : ℝ) (hU : U < 0) : occurrenceCutoff U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have := (mem_occurrenceCutoff i U).mp hi
  linarith [abs_nonneg (occurrenceOrdinate i)]

theorem occurrenceCutoff_exhausts (i : ZeroOccurrence) :
    ∀ᶠ n : ℕ in atTop, i ∈ occurrenceCutoff n := by
  obtain ⟨N, hN⟩ := exists_nat_ge |occurrenceOrdinate i|
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (mem_occurrenceCutoff i n).mpr (hN.trans (by exact_mod_cast hn))

theorem occurrence_ordinate_finite (γ : ℝ) :
    Set.Finite {i : ZeroOccurrence | occurrenceOrdinate i = γ} := by
  apply (occurrence_height_finite |γ|).subset
  intro i hi
  change |occurrenceOrdinate i| ≤ |γ|
  rw [hi]

instance : Countable ZeroOccurrence := by
  have h : (Set.univ : Set ZeroOccurrence) = ⋃ n : ℕ, ↑(occurrenceCutoff n) := by
    ext i
    simp only [Set.mem_univ, Set.mem_iUnion, Finset.mem_coe, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge |occurrenceOrdinate i|
    exact ⟨n, (mem_occurrenceCutoff i n).mpr hn⟩
  apply Set.countable_univ_iff.mp
  rw [h]
  exact Set.countable_iUnion (fun n => (occurrenceCutoff n).countable_toSet)

theorem zero_occurrences_countable : Countable ZeroOccurrence := inferInstance

end
end HigherCorrelations
