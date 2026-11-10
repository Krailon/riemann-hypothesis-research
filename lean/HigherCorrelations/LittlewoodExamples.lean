import HigherCorrelations.LittlewoodZeta

/-! UNCONDITIONAL. Exact constant, repeated-zero and normalization checks. -/
namespace HigherCorrelations
noncomputable section
open Complex Set
open scoped Classical

theorem littlewood_constant_boundary (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (w : ℂ) (hw : w ≠ 0) (k : ℂ) (hk : exp k = w) :
    littlewoodBoundary (fun _ => w) a b c d k = 0 := by
  have h : LittlewoodRectangle (fun _ => w) a b c d := ⟨hab,hcd,by fun_prop,fun _ _ => hw⟩
  have he := littlewood_identity h ∅ (by simp [hw]) k hk
  simpa [littlewoodMass] using he.symm

theorem littlewood_repeated_zero (a b c d : ℝ) (ρ : ℂ) (m : ℕ) (hm : 0 < m)
    (ha : a < ρ.re) (hb : ρ.re < b) (hc : c < ρ.im) (hd : ρ.im < d)
    (k : ℂ) (hk : exp k = (b+c*I-ρ)^m) :
    littlewoodBoundary (fun s => (s-ρ)^m) a b c d k = 2*Real.pi*(m:ℝ)*(ρ.re-a) := by
  have hab : a < b := ha.trans hb
  have hcd : c < d := hc.trans hd
  have hr : ρ ∈ Rectangle (a+c*I) (b+d*I) := by
    simp [Rectangle, mem_reProdIm, uIcc_of_le hab.le, uIcc_of_le hcd.le,
      ha.le,hb.le,hc.le,hd.le]
  have hbr : ρ ∉ RectangleBorder (a+c*I) (b+d*I) := by
    simp [RectangleBorder, mem_reProdIm, uIcc_of_le hab.le, uIcc_of_le hcd.le,
      ne_of_gt ha,ne_of_lt hb,ne_of_gt hc,ne_of_lt hd]
  have h : LittlewoodRectangle (fun s => (s-ρ)^m) a b c d := by
    refine ⟨hab,hcd,by fun_prop,?_⟩
    intro s hs hz
    have he : s = ρ := sub_eq_zero.mp ((pow_eq_zero_iff (Nat.ne_of_gt hm)).mp hz)
    exact hbr (he ▸ hs)
  have hZ : ∀ s, s ∈ ({ρ} : Finset ℂ) ↔ s ∈ Rectangle (a+c*I) (b+d*I) ∧ (s-ρ)^m = 0 := by
    intro s
    simp only [Finset.mem_singleton, pow_eq_zero_iff (Nat.ne_of_gt hm), sub_eq_zero]
    exact ⟨fun he => ⟨he ▸ hr,he⟩,And.right⟩
  have hord : analyticOrderNatAt (fun s : ℂ => (s-ρ)^m) ρ = m := by
    change (analyticOrderAt ((· - ρ) ^ m) ρ).toNat = m
    simp [analyticOrderAt_centeredMonomial]
  rw [← littlewood_identity h {ρ} hZ k hk]
  simp [littlewoodMass, hord, mul_assoc]

end
end HigherCorrelations
