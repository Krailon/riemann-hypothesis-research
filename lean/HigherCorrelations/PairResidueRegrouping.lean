import HigherCorrelations.PairContourPoleSets
import HigherCorrelations.PairTrivialZeros

/-! UNCONDITIONAL finite residue regrouping with actual analytic multiplicities. -/
namespace HigherCorrelations
noncomputable section
open Complex
open scoped BigOperators

theorem pair_occurrenceCutoff_sigma (U : ℝ) :
    occurrenceCutoff U = (pairStripZeros U).sigma (fun ρ => Finset.univ) := by
  classical
  ext i
  simp [mem_occurrenceCutoff, pairStripZeros, occurrenceOrdinate, occurrenceValue]

theorem pairZeroPoints_residue_sum (X t U : ℝ) :
    ∑ z ∈ pairZeroPoints U, residue (pairContourIntegrand X t) z =
      ∑ i ∈ occurrenceCutoff U, pairZeroTerm i (X,t) := by
  classical
  rw [pairZeroPoints, Finset.sum_image (fun a _ b _ he => Subtype.ext he),
    pair_occurrenceCutoff_sigma, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro ρ hρ
  let i : ZeroOccurrence := ⟨ρ,⟨0,zeroMultiplicity_pos ρ⟩⟩
  have hr := pairContour_residue_zero X t i
  change residue (pairContourIntegrand X t) ρ.val = _ at hr
  rw [hr]
  have he (j : Fin (zeroMultiplicity ρ)) : pairZeroTerm ⟨ρ,j⟩ (X,t) = pairZeroTerm i (X,t) := rfl
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rfl

theorem pairTrivialPoints_residue_sum (X t : ℝ) (M : ℕ) :
    ∑ z ∈ pairTrivialPoints M, residue (pairContourIntegrand X t) z =
      -(∑ n ∈ Finset.range M, pairTrivialTerm n (X,t)) := by
  classical
  rw [pairTrivialPoints, Finset.sum_image]
  · simp_rw [pairContour_residue_trivial]
    rw [Finset.sum_neg_distrib]
  · intro a _ b _ hab
    have hr := congrArg Complex.re hab
    simp at hr
    exact hr

theorem pairContour_candidate_residue_sum (X t U : ℝ) (M : ℕ) (hX : 0 < X) :
    ∑ z ∈ pairContourPoleCandidates M U t, residue (pairContourIntegrand X t) z =
      (∑ i ∈ occurrenceCutoff U, pairZeroTerm i (X,t)) - pairPoleCorrection (X,t) -
        (∑ n ∈ Finset.range M, pairTrivialTerm n (X,t)) -
        (X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1)/riemannZeta (pairSpectralPoint t+1)) +
        pairShiftCorrection (X,t) := by
  classical
  let E : Finset ℂ := {1,pairSpectralPoint t+1,pairSpectralPoint t-1}
  have hz : Disjoint E (pairZeroPoints U) := by
    apply Finset.disjoint_left.mpr
    intro z he hz
    have hb := (mem_pairZeroPoints z U).mp hz
    simp only [E,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl|rfl|rfl <;> norm_num [pairSpectralPoint] at hb
  have ht : Disjoint (E ∪ pairZeroPoints U) (pairTrivialPoints M) := by
    apply Finset.disjoint_left.mpr
    intro z he ht
    obtain ⟨n,hn,rfl⟩ := (mem_pairTrivialPoints z M).mp ht
    have hn0 := Nat.cast_nonneg (α:=ℝ) n
    rcases Finset.mem_union.mp he with he | he
    · simp only [E,Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with he|he|he <;> have hr := congrArg Complex.re he <;>
        norm_num [pairSpectralPoint] at hr <;> linarith
    · have hb := (mem_pairZeroPoints _ U).mp he
      norm_num at hb
      linarith [hb.2.1]
  change ∑ z ∈ (E ∪ pairZeroPoints U) ∪ pairTrivialPoints M, _ = _
  rw [Finset.sum_union ht,Finset.sum_union hz,pairZeroPoints_residue_sum,pairTrivialPoints_residue_sum]
  have hp : (1:ℂ) ≠ pairSpectralPoint t+1 := by
    intro h; have hr := congrArg Complex.re h; norm_num [pairSpectralPoint] at hr
  have hm : (1:ℂ) ≠ pairSpectralPoint t-1 := by
    intro h; have hr := congrArg Complex.re h; norm_num [pairSpectralPoint] at hr
  have hpm : pairSpectralPoint t+1 ≠ pairSpectralPoint t-1 := by
    intro h; have hr := congrArg Complex.re h; norm_num [pairSpectralPoint] at hr
  have he : ∑ z ∈ E, residue (pairContourIntegrand X t) z =
      -pairPoleCorrection (X,t) - (X:ℂ)*(deriv riemannZeta (pairSpectralPoint t+1)/
        riemannZeta (pairSpectralPoint t+1)) + pairShiftCorrection (X,t) := by
    simp [E,hp,hm,hpm,pairContour_residue_pole,pairContour_residue_plus X t hX,
      pairContour_residue_minus X t hX]
    ring
  rw [he]
  ring

end
end HigherCorrelations
