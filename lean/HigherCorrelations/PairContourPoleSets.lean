import HigherCorrelations.PairZeroClassification
import HigherCorrelations.PairXiZeros

/-! UNCONDITIONAL finite pole bookkeeping. Complex zeros are listed once here;
analytic multiplicities are restored in the residue-to-occurrence identity. -/
namespace HigherCorrelations
noncomputable section
open Complex
open scoped BigOperators

def pairStripZeros (U : ℝ) : Finset StripZero := (stripZero_height_finite U).toFinset

def pairZeroPoints (U : ℝ) : Finset ℂ := by
  classical
  exact (pairStripZeros U).image Subtype.val

def pairTrivialPoints (M : ℕ) : Finset ℂ := by
  classical
  exact (Finset.range M).image (fun n : ℕ => -2*(n+1:ℂ))

def pairContourPoleCandidates (M : ℕ) (U t : ℝ) : Finset ℂ := by
  classical
  exact {1,pairSpectralPoint t+1,pairSpectralPoint t-1} ∪ pairZeroPoints U ∪ pairTrivialPoints M

@[simp] theorem mem_pairZeroPoints (z : ℂ) (U : ℝ) :
    z ∈ pairZeroPoints U ↔ riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ U := by
  classical
  simp only [pairZeroPoints, Finset.mem_image]
  constructor
  · rintro ⟨ρ,hρ,rfl⟩
    exact ⟨ρ.property.1,ρ.property.2.1,ρ.property.2.2,by simpa [pairStripZeros] using hρ⟩
  · rintro ⟨hζ,hlo,hhi,hU⟩
    exact ⟨⟨z,hζ,hlo,hhi⟩,by simpa [pairStripZeros] using hU,rfl⟩

@[simp] theorem mem_pairTrivialPoints (z : ℂ) (M : ℕ) :
    z ∈ pairTrivialPoints M ↔ ∃ n : ℕ, n < M ∧ z = -2*(n+1:ℂ) := by
  classical
  simp only [pairTrivialPoints, Finset.mem_image, Finset.mem_range]
  constructor <;> rintro ⟨n,hn,hz⟩ <;> exact ⟨n,hn,hz.symm⟩

@[simp] theorem mem_pairContourPoleCandidates (z : ℂ) (M : ℕ) (U t : ℝ) :
    z ∈ pairContourPoleCandidates M U t ↔
      z = 1 ∨ z = pairSpectralPoint t+1 ∨ z = pairSpectralPoint t-1 ∨
      z ∈ pairZeroPoints U ∨ z ∈ pairTrivialPoints M := by
  classical
  simp [pairContourPoleCandidates, or_assoc]

theorem pairContourPoleCandidates_bounds (M : ℕ) (U t ε : ℝ)
    (hU : 0 < U) (ht : |t| < U) (hε : 0 < ε)
    (hgap : ∀ i : ZeroOccurrence, ε ≤ |U-occurrenceOrdinate i|)
    (z : ℂ) (hz : z ∈ pairContourPoleCandidates M U t) :
    -(2*(M:ℝ)+1) < z.re ∧ z.re < 5/2 ∧ -U < z.im ∧ z.im < U := by
  have hM := Nat.cast_nonneg (α:=ℝ) M
  rcases (mem_pairContourPoleCandidates z M U t).mp hz with rfl|rfl|rfl|hz|hz
  · norm_num; constructor <;> linarith
  · norm_num [pairSpectralPoint]
    exact ⟨by linarith,(abs_lt.mp ht).1,(abs_lt.mp ht).2⟩
  · norm_num [pairSpectralPoint]
    exact ⟨by linarith,(abs_lt.mp ht).1,(abs_lt.mp ht).2⟩
  · obtain ⟨hζ,hlo,hhi,hheight⟩ := (mem_pairZeroPoints z U).mp hz
    let ρ : StripZero := ⟨z,hζ,hlo,hhi⟩
    let i : ZeroOccurrence := ⟨ρ,⟨0,zeroMultiplicity_pos ρ⟩⟩
    have hg := hgap i
    have hgn := pairGoodHeight_gap_neg U ε hgap i
    change ε ≤ |U-z.im| at hg
    change ε ≤ |-U-z.im| at hgn
    have hn : z.im ≠ U := by intro he; simp [he] at hg; linarith
    have hp : z.im ≠ -U := by intro he; simp [he] at hgn; linarith
    exact ⟨by linarith,by linarith,lt_of_le_of_ne (abs_le.mp hheight).1 hp.symm,
      lt_of_le_of_ne (abs_le.mp hheight).2 hn⟩
  · obtain ⟨n,hn,rfl⟩ := (mem_pairTrivialPoints z M).mp hz
    have hn' : (n:ℝ)+1 ≤ M := by exact_mod_cast hn
    have hn0 := Nat.cast_nonneg (α:=ℝ) n
    norm_num
    exact ⟨by linarith,by linarith,hU⟩

end
end HigherCorrelations
