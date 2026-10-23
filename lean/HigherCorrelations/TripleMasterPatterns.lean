import HigherCorrelations.TripleMasterPatternDefinitions
import HigherCorrelations.TripleMasterIdentity

/-! UNCONDITIONAL five occurrence-index subseries of the exact master identity.
Absolute integral-norm convergence is inherited before restricting interchanges.
The three partial diagonals retain their different third-slot conjugations. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

private def allEqualEquiv : ZeroOccurrence ≃ MasterPatternTriple .allEqual where
  toFun i := ⟨![i,i,i], by simp [classifyTriple]⟩
  invFun v := v.val 0
  left_inv i := rfl
  right_inv v := by
    apply Subtype.ext
    have h := (classifyTriple_iff v.val .allEqual).mp v.property
    dsimp [HasPattern] at h
    funext r
    fin_cases r <;> simp_all

private def only01Equiv : MasterUnequalPair ≃ MasterPatternTriple .only01 where
  toFun q := ⟨![q.val.1,q.val.1,q.val.2], by simp [classifyTriple,q.property]⟩
  invFun v := ⟨(v.val 0,v.val 2), ((classifyTriple_iff v.val .only01).mp v.property).2⟩
  left_inv q := by rfl
  right_inv v := by
    apply Subtype.ext
    have h := (classifyTriple_iff v.val .only01).mp v.property
    dsimp [HasPattern] at h
    funext r
    fin_cases r <;> simp_all

private def only02Equiv : MasterUnequalPair ≃ MasterPatternTriple .only02 where
  toFun q := ⟨![q.val.1,q.val.2,q.val.1], by simp [classifyTriple,q.property]⟩
  invFun v := ⟨(v.val 0,v.val 1), ((classifyTriple_iff v.val .only02).mp v.property).2⟩
  left_inv q := by rfl
  right_inv v := by
    apply Subtype.ext
    have h := (classifyTriple_iff v.val .only02).mp v.property
    dsimp [HasPattern] at h
    funext r
    fin_cases r <;> simp_all

private def only12Equiv : MasterUnequalPair ≃ MasterPatternTriple .only12 where
  toFun q := ⟨![q.val.1,q.val.2,q.val.2], by simp [classifyTriple,q.property]⟩
  invFun v := ⟨(v.val 0,v.val 1), ((classifyTriple_iff v.val .only12).mp v.property).2⟩
  left_inv q := by rfl
  right_inv v := by
    apply Subtype.ext
    have h := (classifyTriple_iff v.val .only12).mp v.property
    dsimp [HasPattern] at h
    funext r
    fin_cases r <;> simp_all

private def allDistinctEquiv : MasterDistinctTriple ≃ MasterPatternTriple .allDistinct where
  toFun v := ⟨v.val, (classifyTriple_iff v.val .allDistinct).mpr v.property⟩
  invFun v := ⟨v.val, (classifyTriple_iff v.val .allDistinct).mp v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tripleMasterPattern_allEqual (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .allEqual =
      ∑' i : ZeroOccurrence, tripleMasterKernelTerm ω T X Y ![i,i,i] := by
  exact (allEqualEquiv.tsum_eq (fun v => tripleMasterKernelTerm ω T X Y v.val)).symm

theorem tripleMasterPattern_only01 (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .only01 =
      ∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.1,q.val.2] := by
  exact (only01Equiv.tsum_eq (fun v => tripleMasterKernelTerm ω T X Y v.val)).symm

theorem tripleMasterPattern_only02 (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .only02 =
      ∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.1] := by
  exact (only02Equiv.tsum_eq (fun v => tripleMasterKernelTerm ω T X Y v.val)).symm

theorem tripleMasterPattern_only12 (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .only12 =
      ∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.2] := by
  exact (only12Equiv.tsum_eq (fun v => tripleMasterKernelTerm ω T X Y v.val)).symm

theorem tripleMasterPattern_allDistinct (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .allDistinct =
      ∑' v : MasterDistinctTriple, tripleMasterKernelTerm ω T X Y v.val := by
  exact (allDistinctEquiv.tsum_eq (fun v => tripleMasterKernelTerm ω T X Y v.val)).symm

theorem tripleMasterKernelTerm_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ‖tripleMasterKernelTerm ω T X Y v‖) := by
  simpa only [tripleMasterKernelTerm, norm_mul, Complex.norm_ofNat] using
    (tripleMaster_kernel_norm_summable ω hω hs T X Y hT hX hY).mul_left 8

theorem tripleMasterPattern_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Summable (fun v : MasterPatternTriple p => ‖tripleMasterKernelTerm ω T X Y v.val‖) :=
  (tripleMasterKernelTerm_norm_summable ω hω hs T X Y hT hX hY).comp_injective Subtype.val_injective

theorem tripleMasterPattern_integralNorm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Summable (fun v : MasterPatternTriple p => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v.val t‖) :=
  (tripleMaster_integralNorm_summable ω hω hs T X Y hT hX hY).comp_injective Subtype.val_injective

theorem tripleMasterPattern_integralNorm_le (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    (∑' v : MasterPatternTriple p, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v.val t‖) ≤
      ∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖ := by
  exact Summable.tsum_subtype_le _ _ (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (tripleMaster_integralNorm_summable ω hω hs T X Y hT hX hY)

theorem tripleMasterPattern_integral_identity (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    tripleMasterPatternSeries ω T X Y p =
      ∫ t : ℝ, ∑' v : MasterPatternTriple p, tripleMasterTerm ω T X Y v.val t := by
  unfold tripleMasterPatternSeries
  simp_rw [show ∀ v, tripleMasterKernelTerm ω T X Y v = ∫ t : ℝ, tripleMasterTerm ω T X Y v t from
    fun v => (tripleMaster_integral_eq_kernel ω T X Y (by linarith) (by linarith) v).symm]
  exact integral_occurrence_sum volume _
    (fun v => tripleMasterTerm_integrable ω hω hs T X Y (by linarith) hX hY v.val)
    (tripleMasterPattern_integralNorm_summable ω hω hs T X Y hT hX hY p)

theorem tripleMaster_pattern_decomposition (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y = ∑ p : TriplePattern, tripleMasterPatternSeries ω T X Y p := by
  classical
  rw [tripleMaster_kernel_identity ω hω hs T X Y hT hX hY, ← tsum_mul_left]
  exact tsum_triple_patterns id (tripleMasterKernelTerm ω T X Y)
    (tripleMasterKernelTerm_norm_summable ω hω hs T X Y hT hX hY)

/-- All five displayed row series are absolutely convergent. -/
theorem tripleMaster_rows_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun i : ZeroOccurrence => ‖tripleMasterKernelTerm ω T X Y ![i,i,i]‖) ∧
    Summable (fun q : MasterUnequalPair => ‖tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.1,q.val.2]‖) ∧
    Summable (fun q : MasterUnequalPair => ‖tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.1]‖) ∧
    Summable (fun q : MasterUnequalPair => ‖tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.2]‖) ∧
    Summable (fun v : MasterDistinctTriple => ‖tripleMasterKernelTerm ω T X Y v.val‖) := by
  have h := tripleMasterKernelTerm_norm_summable ω hω hs T X Y hT hX hY
  have h0 : Function.Injective (fun i : ZeroOccurrence => (![i,i,i] : MasterTriple)) := by
    intro i j hij
    simpa using congrFun hij 0
  have h01 : Function.Injective (fun q : MasterUnequalPair =>
      (![q.val.1,q.val.1,q.val.2] : MasterTriple)) := by
    intro q r hqr
    apply Subtype.ext
    apply Prod.ext
    · simpa using congrFun hqr 0
    · simpa using congrFun hqr 2
  have h02 : Function.Injective (fun q : MasterUnequalPair =>
      (![q.val.1,q.val.2,q.val.1] : MasterTriple)) := by
    intro q r hqr
    apply Subtype.ext
    apply Prod.ext
    · simpa using congrFun hqr 0
    · simpa using congrFun hqr 1
  have h12 : Function.Injective (fun q : MasterUnequalPair =>
      (![q.val.1,q.val.2,q.val.2] : MasterTriple)) := by
    intro q r hqr
    apply Subtype.ext
    apply Prod.ext
    · simpa using congrFun hqr 0
    · simpa using congrFun hqr 1
  exact ⟨h.comp_injective h0, h.comp_injective h01, h.comp_injective h02,
    h.comp_injective h12, h.comp_injective Subtype.val_injective⟩

/-- The manuscript's five rows, with each B retaining its factor eight. -/
theorem tripleMaster_five_subseries (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      (∑' i : ZeroOccurrence, tripleMasterKernelTerm ω T X Y ![i,i,i]) +
      (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.1,q.val.2]) +
      (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.1]) +
      (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.2]) +
      (∑' v : MasterDistinctTriple, tripleMasterKernelTerm ω T X Y v.val) := by
  have h := tripleMaster_pattern_decomposition ω hω hs T X Y hT hX hY
  rw [show (Finset.univ : Finset TriplePattern) =
    {.allEqual,.only01,.only02,.only12,.allDistinct} from rfl] at h
  simpa [tripleMasterPattern_allEqual, tripleMasterPattern_only01,
    tripleMasterPattern_only02, tripleMasterPattern_only12,
    tripleMasterPattern_allDistinct, add_assoc] using h

theorem tripleMasterPattern_pointwise_summable (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) (t : ℝ) :
    Summable (fun v : MasterPatternTriple p => ‖tripleMasterTerm ω T X Y v.val t‖) :=
  (tripleMaster_pointwise_summable ω hs T X Y hT hX hY t).comp_injective Subtype.val_injective

theorem tripleMasterPattern_finite_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y)
    (S : Fin 3 → Finset ZeroOccurrence) (p : TriplePattern) :
    (∫ t : ℝ, ∑ v ∈ patternDomain id S p, tripleMasterTerm ω T X Y v t) =
      ∑ v ∈ patternDomain id S p, tripleMasterKernelTerm ω T X Y v := by
  classical
  rw [integral_finsetSum _ (fun v _ =>
    tripleMasterTerm_integrable ω hω hs T X Y (by linarith) hX hY v)]
  apply Finset.sum_congr rfl
  intro v _
  exact tripleMaster_integral_eq_kernel ω T X Y (by linarith) (by linarith) v

private theorem pattern_cutoff_limit {K : Type*} (l : Filter K)
    (S : K → Fin 3 → Finset ZeroOccurrence)
    (hS : ∀ r i, ∀ᶠ k in l, i ∈ S k r)
    (B : MasterTriple → ℂ) (hB : Summable (fun v => ‖B v‖)) (p : TriplePattern) :
    Tendsto (fun k => ∑ v ∈ patternDomain id (S k) p, B v) l
      (𝓝 (∑' v : MasterPatternTriple p, B v.val)) := by
  classical
  have h := occurrence_cutoff_limit l
    (fun k => (tripleDomain (S k)).subtype (fun v => classifyTriple v = p))
    (fun v => by
      filter_upwards [Filter.eventually_all.mpr (fun r => hS r (v.val r))] with k hk
      simpa only [Finset.mem_subtype, tripleDomain, Fintype.mem_piFinset] using hk)
    (fun v : MasterPatternTriple p => B v.val) (hB.comp_injective Subtype.val_injective)
  simpa only [Finset.sum_subtype_eq_sum_filter, patternDomain, Function.comp_def, id_eq] using h

theorem tripleMasterPattern_independent_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∑ v ∈ patternDomain id S p, tripleMasterKernelTerm ω T X Y v) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by
  classical
  apply pattern_cutoff_limit atTop id _ _
    (tripleMasterKernelTerm_norm_summable ω hω hs T X Y hT hX hY)
  intro r i
  exact eventually_atTop.mpr ⟨fun _ => {i},fun S hS => hS r (Finset.mem_singleton_self i)⟩

theorem tripleMasterPattern_height_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∑ v ∈ patternDomain id (fun r => occurrenceCutoff (U r)) p,
        tripleMasterKernelTerm ω T X Y v) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by
  apply pattern_cutoff_limit atTop (fun (U : Fin 3 → ℝ) r => occurrenceCutoff (U r)) _
    (tripleMasterKernelTerm ω T X Y)
    (tripleMasterKernelTerm_norm_summable ω hω hs T X Y hT hX hY) p
  intro r i
  apply eventually_atTop.mpr
  exact ⟨fun _ => |occurrenceOrdinate i|,fun U hU => (mem_occurrenceCutoff _ _).mpr (hU r)⟩

theorem tripleMasterPattern_integral_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∫ t : ℝ, ∑ v ∈ patternDomain id S p, tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by
  classical
  simpa only [tripleMasterPattern_finite_integral ω hω hs T X Y hT hX hY] using
    tripleMasterPattern_independent_cutoff ω hω hs T X Y hT hX hY p

theorem tripleMasterPattern_integral_height_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun U : Fin 3 → ℝ => ∫ t : ℝ,
      ∑ v ∈ patternDomain id (fun r => occurrenceCutoff (U r)) p,
        tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by
  classical
  simpa only [tripleMasterPattern_finite_integral ω hω hs T X Y hT hX hY] using
    tripleMasterPattern_height_cutoff ω hω hs T X Y hT hX hY p

/-- Each pattern retains the full factor eight at the unit-base endpoint. -/
theorem tripleMasterPattern_minimal (ω : ℝ → ℝ) (p : TriplePattern) :
    tripleMasterPatternSeries ω 3 1 1 p =
      8 * ∑' v : MasterPatternTriple p, tripleMasterKernel ω 3 v.val := by
  simp only [tripleMasterPatternSeries, tripleMasterKernelTerm, tripleMasterCoefficient,
    Real.log_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  exact tsum_mul_left

/-- Empty membership in any slot annihilates every pattern, including the diagonal. -/
theorem tripleMasterPattern_empty_slot (ω : ℝ → ℝ) (T X Y : ℝ)
    (S : Fin 3 → Finset ZeroOccurrence) (r : Fin 3) (hS : S r = ∅) (p : TriplePattern) :
    (∑ v ∈ patternDomain id S p, tripleMasterKernelTerm ω T X Y v) = 0 := by
  classical
  have he : tripleDomain S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := (Fintype.mem_piFinset.mp hv) r
    simp [hS] at hh
  simp [patternDomain, he]

end
end HigherCorrelations
