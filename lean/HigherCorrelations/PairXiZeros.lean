import HigherCorrelations.PairGoodHeightSelection
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-! The zeros in the audited Hadamard product are actual nontrivial zeta zeros.
UNCONDITIONAL; no replacement of their real parts is made. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairXi_ne_zero_right (z : ℂ) (hz : 1 ≤ z.re) : riemannXi z ≠ 0 := by
  by_cases h1 : z = 1
  · subst z
    have hf := riemannXi_one_sub 0
    have he : riemannXi 1 = 1/2 := by simpa [riemannXi_zero] using hf
    rw [he]; norm_num
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1]
  apply div_ne_zero _ (by norm_num)
  apply mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  have he := riemannZeta_def_of_ne_zero h0
  intro he0
  rw [he0, zero_div] at he
  exact riemannZeta_ne_zero_of_one_le_re hz he

theorem pairXi_zero_isStripZero (z : ℂ) (hz : riemannXi z = 0) :
    IsCriticalStripZero z := by
  have hu : z.re < 1 := by
    by_contra h
    exact pairXi_ne_zero_right z (le_of_not_gt h) hz
  have hl : 0 < z.re := by
    by_contra h
    have hw : 1 ≤ (1-z).re := by simp; linarith [le_of_not_gt h]
    exact pairXi_ne_zero_right (1-z) hw (by rw [riemannXi_one_sub, hz])
  have h0 : z ≠ 0 := by intro h; simp [h] at hl
  have h1 : z ≠ 1 := by intro h; simp [h] at hu
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1] at hz
  have hc : completedRiemannZeta z = 0 := by
    have hm := (div_eq_zero_iff.mp hz).resolve_right (by norm_num)
    exact (mul_eq_zero.mp hm).resolve_left (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  refine ⟨?_,hl,hu⟩
  rw [riemannZeta_def_of_ne_zero h0, hc, zero_div]

theorem pairGoodHeight_zeta_ne_zero (U ε : ℝ) (hU : U ≠ 0) (hε : 0 < ε)
    (hgap : ∀ i : ZeroOccurrence, ε ≤ |U-occurrenceOrdinate i|) (σ : ℝ) :
    riemannZeta ((σ:ℂ)+(U:ℂ)*I) ≠ 0 := by
  intro hz
  have hstrip : IsCriticalStripZero ((σ:ℂ)+(U:ℂ)*I) := by
    refine ⟨hz,?_,?_⟩
    · by_contra h
      exact Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero
        (le_of_not_gt h) (by simpa using hU) hz
    · by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hz
  let ρ : StripZero := ⟨_,hstrip⟩
  let i : ZeroOccurrence := ⟨ρ,⟨0,zeroMultiplicity_pos ρ⟩⟩
  have hb := hgap i
  have he : occurrenceOrdinate i = U := by simp [i,ρ,occurrenceOrdinate,occurrenceValue]
  rw [he, sub_self, abs_zero] at hb
  linarith

theorem pairXi_index_zero
    (p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    riemannXi (Hadamard.divisorZeroIndex₀_val p) = 0 := by
  by_contra hn
  have ha := differentiable_riemannXi.analyticAt (Hadamard.divisorZeroIndex₀_val p)
  have horder : meromorphicOrderAt riemannXi (Hadamard.divisorZeroIndex₀_val p) = 0 := by
    rw [ha.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hn)]
    rfl
  have hm : MeromorphicOn riemannXi (Set.univ : Set ℂ) :=
    fun z _ => (differentiable_riemannXi.analyticAt z).meromorphicAt
  have hd := Hadamard.divisorZeroIndex₀_val_mem_divisor_support p
  rw [MeromorphicOn.divisor_apply hm (Set.mem_univ _), horder] at hd
  simp at hd

theorem pairXi_index_gap (U ε : ℝ)
    (hgap : ∀ i : ZeroOccurrence, ε ≤ |U-occurrenceOrdinate i|)
    (p : Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ε ≤ |U-(Hadamard.divisorZeroIndex₀_val p).im| := by
  let ρ : StripZero := ⟨_,pairXi_zero_isStripZero _ (pairXi_index_zero p)⟩
  exact hgap ⟨ρ,⟨0,zeroMultiplicity_pos ρ⟩⟩

end
end HigherCorrelations
