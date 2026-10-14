import HigherCorrelations.PairContourPoleSets
import HigherCorrelations.PairContourMeromorphic

/-! UNCONDITIONAL finite rectangle residue identity. All possible poles are
included in the finite sum, even if a kernel pole is removable for a particular t. -/
namespace HigherCorrelations
noncomputable section
open Complex

def pairRectangleLeft (M : ℕ) (U : ℝ) : ℂ := -(2*(M:ℂ)+1)-(U:ℂ)*I

def pairRectangleRight (U : ℝ) : ℂ := 5/2+(U:ℂ)*I

theorem pairRectangle_mem (M : ℕ) (U : ℝ) (hU : 0 ≤ U) (z : ℂ) :
    z ∈ Rectangle (pairRectangleLeft M U) (pairRectangleRight U) ↔
      -(2*(M:ℝ)+1) ≤ z.re ∧ z.re ≤ 5/2 ∧ -U ≤ z.im ∧ z.im ≤ U := by
  have hre : (pairRectangleLeft M U).re ≤ (pairRectangleRight U).re := by
    simp [pairRectangleLeft,pairRectangleRight]
    have := Nat.cast_nonneg (α:=ℝ) M
    linarith
  have him : (pairRectangleLeft M U).im ≤ (pairRectangleRight U).im := by
    simp [pairRectangleLeft,pairRectangleRight]; linarith
  rw [mem_Rect hre him]
  simp [pairRectangleLeft,pairRectangleRight]

theorem pairContour_analytic_outside_candidates (X t U : ℝ) (M : ℕ) (hU : 0 ≤ U)
    (z : ℂ) (hz : z ∈ Rectangle (pairRectangleLeft M U) (pairRectangleRight U))
    (hn : z ∉ pairContourPoleCandidates M U t) : AnalyticAt ℂ (pairContourIntegrand X t) z := by
  have hnot := not_congr (mem_pairContourPoleCandidates z M U t) |>.mp hn
  push Not at hnot
  obtain ⟨h₁,hp,hm,hzero,htrivial⟩ := hnot
  apply pairContourIntegrand_analyticAt X t z h₁ _ hp hm
  intro hζ
  rcases pairZero_classification z hζ with hstrip | ⟨n,rfl⟩
  · apply hzero
    exact (mem_pairZeroPoints z U).mpr ⟨hζ,hstrip.1,hstrip.2,
      abs_le.mpr ⟨((pairRectangle_mem M U hU z).mp hz).2.2.1,
        ((pairRectangle_mem M U hU z).mp hz).2.2.2⟩⟩
  · apply htrivial
    apply (mem_pairTrivialPoints _ M).mpr
    refine ⟨n,?_,rfl⟩
    have hh := ((pairRectangle_mem M U hU _).mp hz).1
    simp at hh
    have hn : (n:ℝ) < (M:ℝ) := by linarith
    exact_mod_cast hn

theorem pairContour_finite_rectangle (X t U ε : ℝ) (M : ℕ)
    (hX : 0 < X) (hU : 0 < U) (ht : |t| < U) (hε : 0 < ε)
    (hgap : ∀ i : ZeroOccurrence, ε ≤ |U-occurrenceOrdinate i|) :
    RectangleIntegral' (pairContourIntegrand X t) (pairRectangleLeft M U) (pairRectangleRight U) =
      ∑ z ∈ pairContourPoleCandidates M U t, residue (pairContourIntegrand X t) z := by
  classical
  let S := pairContourPoleCandidates M U t
  let R := Rectangle (pairRectangleLeft M U) (pairRectangleRight U)
  let P := {z : ℂ | meromorphicOrderAt (pairContourIntegrand X t) z < 0}
  have hs (z : ℂ) (hz : z ∈ S) := pairContourPoleCandidates_bounds M U t ε hU ht hε hgap z hz
  have hsub : (S : Set ℂ) ⊆ R := by
    intro z hz
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hs z hz
    exact (pairRectangle_mem M U hU.le z).mpr ⟨h₁.le,h₂.le,h₃.le,h₄.le⟩
  have hpoles : R ∩ P ⊆ (S : Set ℂ) := by
    intro z hz
    by_contra hn
    have ha := pairContour_analytic_outside_candidates X t U M hU.le z hz.1 hn
    exact (not_lt_of_ge ha.meromorphicOrderAt_nonneg) hz.2
  have hfinite : (R ∩ P).Finite := S.finite_toSet.subset hpoles
  have hborder : Disjoint (RectangleBorder (pairRectangleLeft M U) (pairRectangleRight U)) P := by
    apply Set.disjoint_left.mpr
    intro z hz hp
    have hsz := hpoles ⟨rectangleBorder_subset_rectangle _ _ hz,hp⟩
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hs z hsz
    have hd := rectangleBorder_disjoint_singleton
      (z := pairRectangleLeft M U) (w := pairRectangleRight U) (p := z)
      (by simpa [pairRectangleLeft,pairRectangleRight] using
        And.intro (ne_of_gt h₁) ⟨ne_of_lt h₂,ne_of_gt h₃,ne_of_lt h₄⟩)
    exact Set.disjoint_left.mp hd hz (Set.mem_singleton z)
  have hre : (pairRectangleLeft M U).re ≤ (pairRectangleRight U).re := by
    simp [pairRectangleLeft,pairRectangleRight]
    have := Nat.cast_nonneg (α:=ℝ) M
    linarith
  have him : (pairRectangleLeft M U).im ≤ (pairRectangleRight U).im := by
    simp [pairRectangleLeft,pairRectangleRight]; linarith
  rw [RectangleIntegral'_eq_sumResiduesIn hre him
    (fun z _ => pairContourIntegrand_meromorphic X t z) hborder hfinite
    ((pairContour_simple_poles X t hX).mono (Set.subset_univ _))]
  have he : R ∩ P = (S : Set ℂ) ∩ P := Set.Subset.antisymm
    (fun _ hz => ⟨hpoles hz,hz.2⟩) (fun _ hz => ⟨hsub hz.1,hz.2⟩)
  rw [sumResiduesIn_inter_eq_of_set_eq he (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (pairContourIntegrand_meromorphic X t z)
      (le_of_not_gt hz))]
  simp only [sumResiduesIn, tsum_fintype]
  exact Finset.sum_attach S (residue (pairContourIntegrand X t))

end
end HigherCorrelations
