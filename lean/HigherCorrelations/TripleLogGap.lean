import HigherCorrelations.TripleLogGapDefinitions
import HigherCorrelations.TripleLogGapFinite

/-! UNCONDITIONAL infinite logarithmic-gap bound. Finite rectangles are bounded
first; every finite subset of the product lies in such a rectangle. Nonnegative
summability then justifies arbitrary independent cutoff removal. -/
namespace HigherCorrelations
noncomputable section

theorem tripleLogEnergyTerm_nonneg (c : LogGapIndex → ℂ) (n : LogGapIndex) :
    0≤tripleLogEnergyTerm c n := by
  have hl : 0≤Real.log (2*n.val) := Real.log_nonneg (by exact_mod_cast (show 1≤2*n.val by omega))
  unfold tripleLogEnergyTerm
  positivity

theorem tripleLogGapTerm_nonneg (c d : LogGapIndex → ℂ) (p : LogGapIndex × LogGapIndex) :
    0≤tripleLogGapTerm c d p := by
  unfold tripleLogGapTerm
  split_ifs <;> positivity

theorem tripleLogGap_rectangle (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d))
    (s t : Finset LogGapIndex) :
    (∑ m ∈ s, ∑ n ∈ t, tripleLogGapTerm c d (m,n)) ≤ tripleLogGapBound c d := by
  classical
  let e : LogGapIndex ↪ ℕ := ⟨Subtype.val,Subtype.val_injective⟩
  let a : ℕ → ℝ := fun n => if h : 2≤n then ‖c ⟨n,h⟩‖ else 0
  let b : ℕ → ℝ := fun n => if h : 2≤n then ‖d ⟨n,h⟩‖ else 0
  have ha (n : ℕ) : 0≤a n := by dsimp [a]; split_ifs <;> positivity
  have hb (n : ℕ) : 0≤b n := by dsimp [b]; split_ifs <;> positivity
  have hh := tripleLogGap_finite (s.map e) (t.map e)
    (fun m hm => by obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hm; exact i.property)
    (fun n hn => by obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hn; exact i.property) a b ha hb
  simp only [Finset.sum_map,Function.Embedding.coeFn_mk] at hh
  have hax (n : LogGapIndex) : a (e n) = ‖c n‖ := dif_pos n.property
  have hbx (n : LogGapIndex) : b (e n) = ‖d n‖ := dif_pos n.property
  simp_rw [hax,hbx] at hh
  have hh' : (∑ m ∈ s, ∑ n ∈ t, tripleLogGapTerm c d (m,n)) ≤
      (∑ m ∈ s, ‖c m‖)*(∑ n ∈ t, ‖d n‖)/Real.log 2 + 4*Real.sqrt 2 *
        Real.sqrt ((∑ m ∈ s, tripleLogEnergyTerm c m)*(∑ n ∈ t, tripleLogEnergyTerm d n)) := by
    simpa only [tripleLogGapTerm,tripleLogEnergyTerm,norm_mul,e,
      Function.Embedding.coeFn_mk,Subtype.val_inj] using hh
  apply hh'.trans
  unfold tripleLogGapBound tripleLogMass tripleLogEnergy
  have hcs := hc.sum_le_tsum s (fun _ _ => norm_nonneg _)
  have hds := hd.sum_le_tsum t (fun _ _ => norm_nonneg _)
  have hces := hec.sum_le_tsum s (fun n _ => tripleLogEnergyTerm_nonneg c n)
  have hdes := hed.sum_le_tsum t (fun n _ => tripleLogEnergyTerm_nonneg d n)
  have hc0 : 0≤∑ n ∈ s, ‖c n‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hd0 : 0≤∑ n ∈ t, ‖d n‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hce0 : 0≤∑ n ∈ s, tripleLogEnergyTerm c n := Finset.sum_nonneg (fun n _ => tripleLogEnergyTerm_nonneg c n)
  have hde0 : 0≤∑ n ∈ t, tripleLogEnergyTerm d n := Finset.sum_nonneg (fun n _ => tripleLogEnergyTerm_nonneg d n)
  apply add_le_add
  · exact div_le_div_of_nonneg_right (mul_le_mul hcs hds hd0 (hc0.trans hcs)) (Real.log_nonneg (by norm_num))
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul hces hdes hde0 (hce0.trans hces))) (by positivity)

theorem tripleLogGap_finite_subset (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d))
    (s : Finset (LogGapIndex × LogGapIndex)) :
    (∑ p ∈ s, tripleLogGapTerm c d p) ≤ tripleLogGapBound c d := by
  classical
  calc
    _ ≤ ∑ p ∈ s.image Prod.fst ×ˢ s.image Prod.snd, tripleLogGapTerm c d p :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_product
        (fun p _ _ => tripleLogGapTerm_nonneg c d p)
    _ = ∑ m ∈ s.image Prod.fst, ∑ n ∈ s.image Prod.snd, tripleLogGapTerm c d (m,n) := Finset.sum_product _ _ _
    _ ≤ _ := tripleLogGap_rectangle c d hc hd hec hed _ _

theorem tripleLogGap_summable (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    Summable (tripleLogGapTerm c d) :=
  summable_of_sum_le (tripleLogGapTerm_nonneg c d) (tripleLogGap_finite_subset c d hc hd hec hed)

theorem tripleLogGap_bound (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    (∑' p, tripleLogGapTerm c d p) ≤ tripleLogGapBound c d :=
  Real.tsum_le_of_sum_le (tripleLogGapTerm_nonneg c d) (tripleLogGap_finite_subset c d hc hd hec hed)

end
end HigherCorrelations
