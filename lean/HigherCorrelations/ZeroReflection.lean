import HigherCorrelations.Definitions
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

/-! UNCONDITIONAL pointwise zero symmetries, with mathlib-only imports.
These do not construct an occurrence enumeration or prove multiplicity matching.
-/
namespace HigherCorrelations

theorem reflected_zero {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    IsCriticalStripZero (1 - ρ) := by
  rcases hρ with ⟨hz, hpos, hlt⟩
  have hn (n : ℕ) : ρ ≠ -(n : ℂ) := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hone : ρ ≠ 1 := by
    intro heq
    simp [heq] at hlt
  constructor
  · rw [riemannZeta_one_sub hn hone, hz, mul_zero]
  · simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith

theorem horizontalReflection_involutive : Function.Involutive horizontalReflection := by
  intro ρ
  simp [horizontalReflection]

theorem horizontalReflection_im (ρ : ℂ) : (horizontalReflection ρ).im = ρ.im := by
  simp [horizontalReflection]

theorem horizontalReflection_displacement (ρ : ℂ) :
    (horizontalReflection ρ).re - (1 / 2 : ℝ) = -(ρ.re - (1 / 2 : ℝ)) := by
  simp only [horizontalReflection, Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

theorem horizontalReflection_zero {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    IsCriticalStripZero (horizontalReflection ρ) := by
  apply reflected_zero
  rcases hρ with ⟨hz, hpos, hlt⟩
  exact ⟨by simp only [riemannZeta_conj, hz, map_zero], by simpa, by simpa⟩

end HigherCorrelations
