import HigherCorrelations.LittlewoodProduct
import HigherCorrelations.LittlewoodZeta

/-! UNCONDITIONAL. Mollified-zeta counting with explicit analyticity and
product boundary nonvanishing. No coefficient, mean-square or density estimate. -/
namespace HigherCorrelations
noncomputable section
open Complex Set

theorem littlewood_mollified_rectangles (M : ℂ → ℂ) (a c d : ℝ)
    (ha : a < 2) (hc : 0 < c) (hcd : c < d)
    (hM : AnalyticOnNhd ℂ M (Rectangle (a+c*I) (2+d*I)))
    (hn : ∀ s ∈ RectangleBorder (a+c*I) (2+d*I), (riemannZeta*M) s ≠ 0) :
    LittlewoodRectangle riemannZeta a 2 c d ∧ LittlewoodRectangle M a 2 c d ∧
      LittlewoodRectangle (riemannZeta*M) a 2 c d := by
  have hz := littlewood_zeta_rectangle a c d ha hc hcd
    (fun s hs => (mul_ne_zero_iff.mp (hn s hs)).1)
  have hm : LittlewoodRectangle M a 2 c d :=
    ⟨ha,hcd,hM,fun s hs => (mul_ne_zero_iff.mp (hn s hs)).2⟩
  exact ⟨hz,hm,hz.mul hm⟩

theorem littlewood_mollified_occurrence_order {M : ℂ → ℂ} {a c d : ℝ}
    (hz : LittlewoodRectangle riemannZeta a 2 c d) (hM : LittlewoodRectangle M a 2 c d)
    (i : ZeroOccurrence) (hi : occurrenceValue i ∈ Rectangle (a+c*I) (2+d*I)) :
    analyticOrderNatAt (riemannZeta*M) (occurrenceValue i) =
      zeroMultiplicity i.1 + analyticOrderNatAt M (occurrenceValue i) :=
  littlewood_product_order hz hM (occurrenceValue i) hi

theorem littlewood_mollified_bound {M : ℂ → ℂ} {a σ c d : ℝ}
    (hz : LittlewoodRectangle riemannZeta a 2 c d) (hM : LittlewoodRectangle M a 2 c d)
    (ha : 0 < a) (hσ : a < σ)
    (k : ℂ) (hk : exp k = (riemannZeta*M) (2+c*I)) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤
      littlewoodBoundary (riemannZeta*M) a 2 c d k / (2*Real.pi*(σ-a)) := by
  obtain ⟨Zf,hZf⟩ := littlewood_zero_set_exists hz
  obtain ⟨Zg,hZg⟩ := littlewood_zero_set_exists hM
  obtain ⟨Z,hZ⟩ := littlewood_zero_set_exists (hz.mul hM)
  rw [← littlewood_zeta_count hz ha hσ Zf hZf]
  exact (Nat.cast_le.mpr (littlewood_product_count_le hz hM Zf Zg Z hZf hZg hZ σ)).trans
    (littlewood_count_bound (hz.mul hM) Z hZ k hk σ hσ)

theorem littlewood_mollified_of_budget {M : ℂ → ℂ} {a σ c d E : ℝ}
    (hz : LittlewoodRectangle riemannZeta a 2 c d) (hM : LittlewoodRectangle M a 2 c d)
    (ha : 0 < a) (hσ : a < σ)
    (k : ℂ) (hk : exp k = (riemannZeta*M) (2+c*I))
    (hE : littlewoodBoundary (riemannZeta*M) a 2 c d k ≤ E) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤ E / (2*Real.pi*(σ-a)) :=
  (littlewood_mollified_bound hz hM ha hσ k hk).trans
    (div_le_div_of_nonneg_right hE (by positivity))

theorem littlewood_mollified_budget_positive_height (M : ℂ → ℂ) (a σ c d E : ℝ)
    (ha : 0 < a) (hσ : a < σ) (hσ' : σ < 1) (hc : 0 < c) (hcd : c < d)
    (hM : AnalyticOnNhd ℂ M (Rectangle (a+c*I) (2+d*I)))
    (hn : ∀ s ∈ RectangleBorder (a+c*I) (2+d*I), (riemannZeta*M) s ≠ 0)
    (hE : littlewoodBoundary (riemannZeta*M) a 2 c d
      (Complex.log ((riemannZeta*M) (2+c*I))) ≤ E) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤ E / (2*Real.pi*(σ-a)) := by
  obtain ⟨hz,hm,hp⟩ := littlewood_mollified_rectangles M a c d (by linarith) hc hcd hM hn
  exact littlewood_mollified_of_budget hz hm ha hσ _
    (Complex.exp_log (hp.horizontal c (Or.inl rfl) 2 ⟨by linarith,le_rfl⟩).2) hE

end
end HigherCorrelations
