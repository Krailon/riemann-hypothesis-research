import HigherCorrelations.ZeroReflection
import OAI.NumberTheory.DirichletL.Nonvanishing
import Mathlib.Tactic

/-! UNCONDITIONAL statements; replay the checks with scripts/reproduce_lean.py.
Source: OpenAI math release, pinned in research/lean-import-pins.json.
The manuscript is a preprint. The right half-plane is open; strip endpoints
are included. No height limit, simplicity or RH assumption is used.
-/
namespace HigherCorrelations

theorem zeta_ne_zero_right {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (_hpole : s ≠ 1) : riemannZeta s ≠ 0 :=
  OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

theorem zero_re_le_seven_eighths {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    ρ.re ≤ (7 / 8 : ℝ) := by
  by_contra h
  exact (OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re (lt_of_not_ge h)) hρ.1

theorem zero_horizontal_strip {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    (1 / 8 : ℝ) ≤ ρ.re ∧ ρ.re ≤ (7 / 8 : ℝ) := by
  have hu := zero_re_le_seven_eighths hρ
  have hl := zero_re_le_seven_eighths (reflected_zero hρ)
  simp only [Complex.sub_re, Complex.one_re] at hl
  constructor <;> linarith

theorem zero_horizontal_displacement {ρ : ℂ} (hρ : IsCriticalStripZero ρ) :
    |ρ.re - (1 / 2 : ℝ)| ≤ (3 / 8 : ℝ) := by
  obtain ⟨hl, hu⟩ := zero_horizontal_strip hρ
  rw [abs_le]
  constructor <;> linarith

theorem indexed_zero_horizontal_strip {I : Type*} (ρ : I → ℂ)
    (hρ : ∀ i, IsCriticalStripZero (ρ i)) (i : I) :
    (1 / 8 : ℝ) ≤ (ρ i).re ∧ (ρ i).re ≤ (7 / 8 : ℝ) ∧
      |(ρ i).re - (1 / 2 : ℝ)| ≤ (3 / 8 : ℝ) :=
  ⟨(zero_horizontal_strip (hρ i)).1, (zero_horizontal_strip (hρ i)).2,
    zero_horizontal_displacement (hρ i)⟩

end HigherCorrelations
