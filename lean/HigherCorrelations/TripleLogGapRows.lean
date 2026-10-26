import HigherCorrelations.TripleLogGapGeometry

/-! UNCONDITIONAL harmonic row bound. Equal indices are never divided by. -/
namespace HigherCorrelations
noncomputable section

theorem tripleLogGap_row (s : Finset ℕ) (m : ℕ) (hm : 2≤m)
    (hs : ∀ n ∈ s, n≤2*m ∧ n≠m) :
    (∑ n ∈ s, 1/|(m:ℝ)-n|) ≤ 4*Real.log (2*m) := by
  classical
  have hleft : (∑ n ∈ s.filter (·<m), 1/|(m:ℝ)-n|) ≤
      ∑ k ∈ Finset.Icc 1 (2*m), (k:ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_injOn (fun n => m-n)
    · intro a ha b hb he
      dsimp at he
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega
    · intro k hk
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
      have h := (Finset.mem_filter.mp hn).2
      simp only [Finset.mem_Icc]
      omega
    · intro n hn
      have h := (Finset.mem_filter.mp hn).2
      rw [Nat.cast_sub h.le,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h.le))]
      simp only [one_div,le_refl]
    · intro k _ _; positivity
  have hright : (∑ n ∈ s.filter (fun n => ¬n<m), 1/|(m:ℝ)-n|) ≤
      ∑ k ∈ Finset.Icc 1 (2*m), (k:ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_injOn (fun n => n-m)
    · intro a ha b hb he
      dsimp at he
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega
    · intro k hk
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hn,hge⟩ := Finset.mem_filter.mp hn
      have h := hs n hn
      simp only [Finset.mem_Icc]
      omega
    · intro n hn
      obtain ⟨hn,hge⟩ := Finset.mem_filter.mp hn
      have hmn : m≤n := by omega
      rw [Nat.cast_sub hmn,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hmn) : (m:ℝ)-n≤0),neg_sub]
      simp only [one_div,le_refl]
    · intro k _ _; positivity
  have hsum : (∑ n ∈ s, 1/|(m:ℝ)-n|) ≤ 2*(harmonic (2*m):ℝ) := by
    have he := Finset.sum_filter_add_sum_filter_not s (fun n => n<m) (fun n => 1/|(m:ℝ)-n|)
    have hh : (∑ k ∈ Finset.Icc 1 (2*m), (k:ℝ)⁻¹) = (harmonic (2*m):ℝ) := by
      simp [harmonic_eq_sum_Icc]
    rw [hh] at hleft hright
    linarith
  have hlog : 1 ≤ Real.log (2*m) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h2
    have h4 : Real.log 4 = 2*Real.log 2 := by
      rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]; ring
    have hmono : Real.log 4 ≤ Real.log (2*m) := Real.log_le_log (by norm_num)
      (by exact_mod_cast (show 4≤2*m by omega))
    linarith
  have hh := harmonic_le_one_add_log (2*m)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hh
  linarith

end
end HigherCorrelations
