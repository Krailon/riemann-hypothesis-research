import HigherCorrelations.TripleBoundaryDefinitions
import HigherCorrelations.TripleBoundaryPointwise
import HigherCorrelations.TripleBoundaryRetainedBounds

/-! UNCONDITIONAL continuous majorant of the exact full-zero residual.
The four summands keep prime, H-word, diagonal/smoothing, and resonance
origins identifiable. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundaryMajorant_continuous (A H D W V T κ : ℝ) :
    Continuous (tripleBoundaryMajorant A H D W V T κ) := by
  unfold tripleBoundaryMajorant
  fun_prop

theorem tripleBoundaryMajorant_nonneg (A H D W V T κ : ℝ)
    (hA : 0≤A) (hH : 0≤H) (hD : 0≤D) (hW : 0≤W) (hV : 0≤V)
    (hT : 2*Real.pi<T) (p : ℝ × ℝ) : 0≤tripleBoundaryMajorant A H D W V T κ p := by
  have ht := tripleTestBase_bounds T hT
  have hT0 : 0<T := by linarith [ht.1]
  have hbase : 0<tripleTestBase T := by linarith [ht.2.1]
  have hb : 0≤Real.log (tripleTestBase T) := (Real.log_pos ht.2.1).le
  have hL : 0≤Real.log (2*T+2) := le_trans (by norm_num) (tripleBudget_height_log T ht.1)
  have hR := tripleResonanceDecayConstant_pos.le
  unfold tripleBoundaryMajorant
  positivity

set_option maxHeartbeats 800000 in
theorem tripleBoundary_majorization : ∃ A : ℝ, 0<A ∧ ∃ H : ℝ, 0<H ∧ ∃ D : ℝ, 0<D ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T κ : ℝ,
    0≤W → (∀ u, ω u≤W) → 2*Real.pi<T → 0<κ →
    ∀ p ∈ tripleQuadrantMargin κ,
    ‖tripleQuadrantRemainder ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)‖ ≤
      tripleBoundaryMajorant A H D W (1+fourierDerivativeL1 ω 1) T κ p := by
  obtain ⟨A,hA,H,hH,D,hD,hpoint⟩ := tripleBoundary_pointwise
  refine ⟨A,hA,H,hH,D,hD,?_⟩
  intro ω hω W T κ hW hωW hT hκ p hp
  let B := tripleTestBase T
  let b := Real.log B
  let L := Real.log (2*T+2)
  let V := 1+fourierDerivativeL1 ω 1
  have ht := tripleTestBase_bounds T hT
  have hT0 : 0<T := by linarith [ht.1]
  have hB : 0<B := by dsimp [B]; linarith [ht.2.1]
  have hb : 0<b := Real.log_pos ht.2.1
  have hL : 0≤L := le_trans (by norm_num) (tripleBudget_height_log T ht.1)
  have hV : 0≤V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hR := tripleResonanceDecayConstant_pos.le
  obtain ⟨hx,hy,hz⟩ := tripleQuadrant_scale_range κ T p hT hp
  obtain ⟨hzt,hzr⟩ := tripleBoundary_product_height κ T hκ.le hT p hp
  have hbox := tripleQuadrantMargin_subset_box κ hκ.le hp
  have hz1 : 1≤B^p.1*B^p.2 := one_le_mul_of_one_le_of_one_le hx hy
  have h1 := mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_right hzr (pow_nonneg hL 4))
      (L^2/(B^p.1*B^p.2)^2+L^3/T)) (mul_nonneg hA.le hV)
  have hdiag := mul_le_mul_of_nonneg_left (tripleBoundary_diagonal_scale (B^p.1) (B^p.2) hx hy)
    (show 0≤D*L by positivity)
  have hg := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (tripleBoundary_G_frequency B ht.2.1 p hbox) (by norm_num : (0:ℝ)≤2)) hT0.le
  have hr := mul_le_mul_of_nonneg_left (tripleBoundary_resonance_scale _ hz1) hR
  have hpow : (B^p.1*B^p.2)^(-(1/4:ℝ)) =
      Real.exp (-((b/4)*p.1))*Real.exp (-((b/4)*p.2)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg hB.le _),
      ← Real.rpow_mul hB.le,← Real.rpow_mul hB.le]
    simp only [Real.rpow_def_of_pos hB]
    congr 2 <;> dsimp [b] <;> congr 1 <;> ring
  have he2 : L^2/(B^p.1*B^p.2)^2 =
      L^2*(Real.exp (-((2*b)*p.1))*Real.exp (-((2*b)*p.2))) := by
    rw [div_eq_mul_one_div,tripleBoundary_inverse_product_square B _ _ hB]
  have he1 : L*(1/B^p.1+1/B^p.2)+L^2/(B^p.1*B^p.2) =
      L*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))+
        L^2*(Real.exp (-(b*p.1))*Real.exp (-(b*p.2))) := by
    simp only [Real.rpow_def_of_pos hB,div_eq_mul_inv,mul_inv,one_mul,← Real.exp_neg,b]
  have hh := hpoint ω hω W T (B^p.1) (B^p.2) hW hωW ht.1 hx hy hzt
  apply hh.trans
  have hall := add_le_add (add_le_add (add_le_add
    (add_le_add h1 (le_refl (H*(1+W)*(L*(1/B^p.1+1/B^p.2)+L^2/(B^p.1*B^p.2))))) hdiag) hg) hr
  rw [he2,he1,hpow,tripleBoundary_inverse_scale B p.1 hB,tripleBoundary_inverse_scale B p.2 hB] at hall
  rw [he2,he1]
  convert hall using 1 <;> dsimp [tripleBoundaryMajorant,L,b,B,V] <;> ring

end
end HigherCorrelations
