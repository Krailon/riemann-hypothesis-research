import HigherCorrelations.PairMeanIntegration

/-! UNCONDITIONAL diagonal extraction and the ordered, strict-bandwidth
nearby-pair bound. Injectivity is explicit and used only to identify the diagonal. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex

theorem pairMeanWeighted_offdiag_bound {ι : Type*} [Countable ι]
    (μ : ι → ℝ) (hμ : Function.Injective μ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (M : ℝ → ℂ) (hM : Integrable M)
    (δ : ℝ) (hδ : 0 < δ)
    (hband : ∀ ξ : ℝ, δ ≤ |ξ| → pairMeanFourier M ξ = 0) :
    ‖(∫ t, M t*(↑(‖pairFrequencySum μ c t‖^2):ℂ)) -
      pairMeanFourier M 0*(pairFrequencyDiagonal c:ℂ)‖ ≤
        (∫ t, ‖M t‖)*pairFrequencyNearby μ c δ := by
  classical
  let A : ι × ι → ℂ := fun p => c p.1*(starRingEnd ℂ) (c p.2)*pairMeanFourier M (μ p.2-μ p.1)
  let B : ι × ι → ℂ := fun p => if p.1 = p.2 then A p else 0
  let O : ι × ι → ℂ := fun p => if p.1 = p.2 then 0 else A p
  let C : ℝ := ∫ t, ‖M t‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hA_bound (p : ι × ι) : ‖A p‖ ≤ C*(‖c p.1‖*‖c p.2‖) := by
    dsimp [A,C]
    rw [norm_mul,norm_mul,Complex.norm_conj,mul_comm (∫ t, ‖M t‖)]
    exact mul_le_mul_of_nonneg_left (pairMeanFourier_norm_bound M _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hprod := (pairFrequency_product_summable c hc).mul_left C
  have hA : Summable A := hprod.of_norm_bounded hA_bound
  have hB : Summable B := hprod.of_norm_bounded fun p => by
    dsimp [B]
    split_ifs
    · exact hA_bound p
    · simp only [norm_zero]
      positivity
  have hO : Summable O := hprod.of_norm_bounded fun p => by
    dsimp [O]
    split_ifs
    · simp only [norm_zero]
      positivity
    · exact hA_bound p
  have hdiag : (∑' p, B p) = pairMeanFourier M 0*(pairFrequencyDiagonal c:ℂ) := by
    rw [hB.tsum_prod]
    have he (i : ι) : (∑' j, B (i,j)) = pairMeanFourier M 0*(↑(‖c i‖^2):ℂ) := by
      simp only [B,Prod.fst,Prod.snd]
      rw [tsum_ite_eq']
      simp only [A,sub_self,Complex.mul_conj',ofReal_pow]
      ring
    simp_rw [he]
    rw [tsum_mul_left, ← Complex.ofReal_tsum]
    rfl
  have hsplit : (∑' p, A p) - pairMeanFourier M 0*(pairFrequencyDiagonal c:ℂ) = ∑' p, O p := by
    rw [← hdiag]
    have he : (fun p => B p+O p) = A := by
      funext p
      dsimp [B,O]
      split_ifs <;> simp
    have hh := hB.tsum_add hO
    rw [he] at hh
    rw [hh]
    abel
  have hnear := (pairFrequency_nearby_summable μ c δ hc).mul_left C
  have hbound (p : ι × ι) : ‖O p‖ ≤ C*(if 0 < |μ p.1-μ p.2| ∧ |μ p.1-μ p.2| < δ
      then ‖c p.1‖*‖c p.2‖ else 0) := by
    by_cases hij : p.1 = p.2
    · simp only [O,if_pos hij,norm_zero]
      split_ifs <;> positivity
    · have hgap : 0 < |μ p.1-μ p.2| := abs_pos.mpr (sub_ne_zero.mpr fun he => hij (hμ he))
      by_cases hsmall : |μ p.1-μ p.2| < δ
      · simpa only [O,if_neg hij, hgap, hsmall, and_self, ite_true] using hA_bound p
      · have hz : pairMeanFourier M (μ p.2-μ p.1) = 0 :=
          hband _ (by rw [abs_sub_comm]; exact le_of_not_gt hsmall)
        simp [O,hij,A,hz,hsmall]
  rw [pairMeanWeighted_square_identity μ c hc M hM,hsplit]
  have h := tsum_of_norm_bounded hnear.hasSum hbound
  simpa only [tsum_mul_left, pairFrequencyNearby, C] using h

end
end HigherCorrelations
