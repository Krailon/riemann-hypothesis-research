import HigherCorrelations.ApproximateFunctionalCutoffs

/-! UNCONDITIONAL bounded-height estimates. The constants in this file depend
on the upper height H. They close the compact part of a future uniform AFE
proof; they do NOT give a constant independent of H. -/
namespace HigherCorrelations
noncomputable section
open Complex Set

theorem afeChi_continuousAt (s : ℂ) (hs : s.im ≠ 0) : ContinuousAt pairChi s := by
  have hreg (n : ℕ) : 1-s ≠ -(n:ℂ) := by
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hg := (differentiableAt_Gamma (1-s) hreg).continuousAt.comp
    (show ContinuousAt (fun z : ℂ => 1-z) s by fun_prop)
  unfold pairChi
  exact (by fun_prop : ContinuousAt (fun z : ℂ =>
    exp (z*(Real.log 2:ℂ)) * exp ((z-1)*(Real.log Real.pi:ℂ)) *
      sin ((Real.pi:ℂ)*z/2)) s).mul hg

theorem afeZetaChi_compact_bound (δ H : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → δ ≤ |t| → |t| ≤ H →
      ‖riemannZeta (afePoint σ t)‖ + ‖pairChi (afePoint σ t)‖ ≤ B := by
  let K : Set (ℝ × ℝ) := Icc (0,-H) (1,H) ∩ {p | δ ≤ |p.2|}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const continuous_snd.abs)
  have hp : Continuous (fun p : ℝ × ℝ => afePoint p.1 p.2) := by
    unfold afePoint; fun_prop
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      ‖riemannZeta (afePoint p.1 p.2)‖ + ‖pairChi (afePoint p.1 p.2)‖) K := by
    intro p hpK
    have hi : (afePoint p.1 p.2).im ≠ 0 := by
      rw [afePoint_im]
      exact (abs_pos.mp (lt_of_lt_of_le hδ hpK.2))
    have hn : afePoint p.1 p.2 ≠ 1 := by
      intro h; apply hi; rw [h]; rfl
    have hz : ContinuousAt (fun p : ℝ × ℝ => riemannZeta (afePoint p.1 p.2)) p :=
      (differentiableAt_riemannZeta hn).continuousAt.comp
        (f := fun p : ℝ × ℝ => afePoint p.1 p.2) hp.continuousAt
    have hχ : ContinuousAt (fun p : ℝ × ℝ => pairChi (afePoint p.1 p.2)) p :=
      (afeChi_continuousAt _ hi).comp
        (f := fun p : ℝ × ℝ => afePoint p.1 p.2) hp.continuousAt
    exact (hz.norm.add hχ.norm).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨|B|+1,by positivity, fun σ t hσ hσ' ht ht' => ?_⟩
  have hmem : (σ,t) ∈ K := ⟨⟨⟨hσ, (abs_le.mp ht').1⟩,
    ⟨hσ', (abs_le.mp ht').2⟩⟩,ht⟩
  have hb := hB (σ,t) hmem
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hb
  exact hb.trans (by have := le_abs_self B; linarith)

theorem afeRemainder_bounded_height (δ H X : ℝ) (hδ : 0 < δ) (hX : 0 ≤ X) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ t x y : ℝ,
      0 ≤ σ → σ ≤ 1 → δ ≤ |t| → |t| ≤ H →
      0 ≤ x → x ≤ X → 0 ≤ y → y ≤ X → ‖afeRemainder (afePoint σ t) x y‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := afeZetaChi_compact_bound δ H hδ
  refine ⟨B+X+B*X+1,by positivity,fun σ t x y hσ hσ' ht ht' hx hx' hy hy' => ?_⟩
  have hz := hbound σ t hσ hσ' ht ht'
  have hP := (afePolynomial_norm_le (afePoint σ t) (by simpa [afePoint] using hσ) hx).trans hx'
  have hQ := (afePolynomial_norm_le (1-afePoint σ t) (by simp [afePoint]; linarith) hy).trans hy'
  have hχ : ‖pairChi (afePoint σ t)‖ ≤ B := by have := norm_nonneg (riemannZeta (afePoint σ t)); linarith
  have hprod := mul_le_mul hχ hQ (norm_nonneg _) hB.le
  unfold afeRemainder
  have htri := norm_sub_le (riemannZeta (afePoint σ t)-afePolynomial (afePoint σ t) x)
    (pairChi (afePoint σ t)*afePolynomial (1-afePoint σ t) y)
  rw [norm_mul] at htri
  have htri' := norm_sub_le (riemannZeta (afePoint σ t)) (afePolynomial (afePoint σ t) x)
  have := norm_nonneg (pairChi (afePoint σ t))
  linarith

theorem afeRemainder_compact_short (H : ℝ) (hH : 2*Real.pi ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t x y : ℝ,
      0 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ |t| → |t| ≤ H →
      1 ≤ x → 1 ≤ y → 2*Real.pi*x*y = |t| →
      ‖afeRemainder (afePoint σ t) x y‖ ≤ C*x^(-σ) := by
  have hp : 1 ≤ 2*Real.pi := by have := Real.pi_gt_three; linarith
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity) hH
  obtain ⟨B,hB,hbound⟩ := afeRemainder_bounded_height (2*Real.pi) H H
    (by positivity) hHpos.le
  refine ⟨B*H,by positivity,fun σ t x y hσ hσ' ht ht' hx hy hxy => ?_⟩
  have hpx : x ≤ 2*Real.pi*x := le_mul_of_one_le_left (by linarith) hp
  have hpy : y ≤ 2*Real.pi*y := le_mul_of_one_le_left (by linarith) hp
  have hxx : x ≤ H := by
    have := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2*Real.pi*x by positivity)
    nlinarith
  have hyy : y ≤ H := by
    have := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*Real.pi*y by positivity)
    nlinarith
  have hb := hbound σ t x y hσ hσ' ht ht' (by linarith) hxx (by linarith) hyy
  have hr : x^(-1:ℝ) ≤ x^(-σ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hinv : H⁻¹ ≤ x⁻¹ := inv_anti₀ (by linarith) hxx
  rw [Real.rpow_neg_one] at hr
  have hh : 1 ≤ H*x^(-σ) := by
    calc
      1 = H*H⁻¹ := (mul_inv_cancel₀ hHpos.ne').symm
      _ ≤ H*x^(-σ) := mul_le_mul_of_nonneg_left (hinv.trans hr) hHpos.le
  have hh' := mul_le_mul_of_nonneg_left hh hB.le
  nlinarith

end
end HigherCorrelations
