import HigherCorrelations.Definitions

/-! Specification only. Comparator checks these statements against the solution.
The intentional `sorry` terms must never be imported by a solution module.
-/
namespace HigherCorrelations

theorem zeta_ne_zero_right {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (_hpole : s ≠ 1) : riemannZeta s ≠ 0 := by sorry

theorem reflected_zero {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    IsCriticalStripZero (1 - ρ) := by sorry

theorem zero_re_le_seven_eighths {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    ρ.re ≤ (7 / 8 : ℝ) := by sorry

theorem zero_horizontal_strip {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    (1 / 8 : ℝ) ≤ ρ.re ∧ ρ.re ≤ (7 / 8 : ℝ) := by sorry

theorem zero_horizontal_displacement {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    |ρ.re - (1 / 2 : ℝ)| ≤ (3 / 8 : ℝ) := by sorry

theorem indexed_zero_horizontal_strip {I : Type*} (ρ : I → ℂ)
    (hρ : ∀ i, IsCriticalStripZero (ρ i)) (i : I) :
    (1 / 8 : ℝ) ≤ (ρ i).re ∧ (ρ i).re ≤ (7 / 8 : ℝ) ∧
      |(ρ i).re - (1 / 2 : ℝ)| ≤ (3 / 8 : ℝ) := by sorry

end HigherCorrelations
