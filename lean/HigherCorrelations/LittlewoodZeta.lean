import HigherCorrelations.LittlewoodCounting
import HigherCorrelations.DensityCountIdentities

/-! UNCONDITIONAL. Actual zeta occurrence adapter, retaining zero-free boundary hypotheses. -/
namespace HigherCorrelations
noncomputable section
open Complex Set
open scoped Classical

theorem littlewood_zeta_count {a σ c d : ℝ}
    (h : LittlewoodRectangle riemannZeta a 2 c d) (ha : 0 < a) (hσ : a < σ)
    (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (a+c*I) (2+d*I) ∧ riemannZeta s = 0) :
    littlewoodRightCount riemannZeta Z σ = (rightDensityWindow c d (σ-1/2)).card := by
  rw [rightDensityWindow_card]
  unfold littlewoodRightCount
  symm
  apply Finset.sum_bij (fun (ρ : StripZero) _ => ρ.val)
  · intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hwin,hγ,hβ⟩
    have hw := (mem_stripZeroInterval _ _ _).mp hwin
    apply Finset.mem_filter.mpr
    refine ⟨(hZ ρ.val).mpr ⟨?_,ρ.property.1⟩,by linarith⟩
    simpa [Rectangle, mem_reProdIm, uIcc_of_le h.horizontal_lt.le,
      uIcc_of_le h.vertical_lt.le] using
      (show (a ≤ ρ.val.re ∧ ρ.val.re ≤ (2:ℝ)) ∧ c ≤ ρ.val.im ∧ ρ.val.im ≤ d from
        ⟨⟨by linarith,by linarith [ρ.property.2.2]⟩,hw⟩)
  · intro ρ hρ τ hτ he
    exact Subtype.ext he
  · intro s hs
    rcases Finset.mem_filter.mp hs with ⟨hs,hβ⟩
    rcases (hZ s).mp hs with ⟨hr,hzero⟩
    have hr' : (a ≤ s.re ∧ s.re ≤ 2) ∧ c ≤ s.im ∧ s.im ≤ d := by
      simpa [Rectangle, mem_reProdIm, uIcc_of_le h.horizontal_lt.le,
        uIcc_of_le h.vertical_lt.le] using hr
    have hlt : s.re < 1 := by
      by_contra hh
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hh) hzero
    let ρ : StripZero := ⟨s,hzero,by linarith, hlt⟩
    have hγ : c < s.im := by
      by_contra hh
      have he : s.im = c := by linarith [hr'.2.1]
      have hb : s ∈ RectangleBorder (a+c*I) (2+d*I) := by
        simp [RectangleBorder, mem_reProdIm, uIcc_of_le h.horizontal_lt.le,
          uIcc_of_le h.vertical_lt.le, he, hr'.1]
      exact h.nonzero s hb hzero
    refine ⟨ρ,Finset.mem_filter.mpr ⟨(mem_stripZeroInterval _ _ _).mpr hr'.2,?_,?_⟩,rfl⟩
    · exact hγ
    · change σ-1/2 < s.re-1/2
      linarith
  · intro ρ hρ
    rfl

theorem littlewood_zeta_bound {a σ c d : ℝ}
    (h : LittlewoodRectangle riemannZeta a 2 c d) (ha : 0 < a) (hσ : a < σ)
    (k : ℂ) (hk : exp k = riemannZeta (2+c*I)) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤
      littlewoodBoundary riemannZeta a 2 c d k / (2*Real.pi*(σ-a)) := by
  obtain ⟨Z,hZ⟩ := littlewood_zero_set_exists h
  rw [← littlewood_zeta_count h ha hσ Z hZ]
  exact littlewood_count_bound h Z hZ k hk σ hσ

theorem littlewood_zeta_of_budget {a σ c d E : ℝ}
    (h : LittlewoodRectangle riemannZeta a 2 c d) (ha : 0 < a) (hσ : a < σ)
    (k : ℂ) (hk : exp k = riemannZeta (2+c*I))
    (hE : littlewoodBoundary riemannZeta a 2 c d k ≤ E) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤ E / (2*Real.pi*(σ-a)) :=
  (littlewood_zeta_bound h ha hσ k hk).trans
    (div_le_div_of_nonneg_right hE (by positivity))

theorem littlewood_zeta_rectangle (a c d : ℝ) (ha : a < 2) (hc : 0 < c) (hcd : c < d)
    (hn : ∀ s ∈ RectangleBorder (a+c*I) (2+d*I), riemannZeta s ≠ 0) :
    LittlewoodRectangle riemannZeta a 2 c d := by
  refine ⟨ha,hcd,?_,hn⟩
  intro s hs
  have hs' : (a ≤ s.re ∧ s.re ≤ 2) ∧ c ≤ s.im ∧ s.im ≤ d := by
    simpa [Rectangle, mem_reProdIm, uIcc_of_le ha.le, uIcc_of_le hcd.le] using hs
  have hi : 0 < s.im := hc.trans_le hs'.2.1
  exact (show DifferentiableOn ℂ riemannZeta {z : ℂ | 0 < z.im} from fun z hz =>
    (differentiableAt_riemannZeta (by intro he; simp [he] at hz)).differentiableWithinAt).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hi)

theorem littlewood_zeta_budget_positive_height (a σ c d E : ℝ)
    (ha : 0 < a) (hσ : a < σ) (hσ' : σ < 1) (hc : 0 < c) (hcd : c < d)
    (hn : ∀ s ∈ RectangleBorder (a+c*I) (2+d*I), riemannZeta s ≠ 0)
    (hE : littlewoodBoundary riemannZeta a 2 c d (Complex.log (riemannZeta (2+c*I))) ≤ E) :
    ((rightDensityWindow c d (σ-1/2)).card : ℝ) ≤ E / (2*Real.pi*(σ-a)) := by
  have h := littlewood_zeta_rectangle a c d (by linarith) hc hcd hn
  exact littlewood_zeta_of_budget h ha hσ _
    (Complex.exp_log (riemannZeta_ne_zero_of_one_lt_re (by simp))) hE

end
end HigherCorrelations
