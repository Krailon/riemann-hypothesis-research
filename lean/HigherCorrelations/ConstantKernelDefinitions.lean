import HigherCorrelations.FiniteDefinitions
import HigherCorrelations.IntegralProfileDefinitions

/-! UNCONDITIONAL definitions for pointwise constant-kernel replacement.
Horizontal slots are anchor first: δ₀, δ₁, δ₂. The rational profile receives
δ₁, δ₂, δ₀, with a positive imaginary anchor center. -/
namespace HigherCorrelations
noncomputable section

def constantKernelParameters (δ : Fin 3 → ℝ) (e : Fin 3 → Bool) : Fin 3 → ℝ :=
  ![if e 1 then -δ 1 else δ 1, if e 2 then -δ 2 else δ 2,
    if e 0 then -δ 0 else δ 0]

def constantKernelEmpty (a d : ℝ) (δ : Fin 3 → ℝ) : ℂ :=
  signCoefficient (fun e => horizontalProfile a d (constantKernelParameters δ e)) ∅

def constantKernelEnergy (a d : ℝ) (δ : Fin 3 → ℝ) : ℝ :=
  a^2+d^2+∑ j, δ j^2

def constantKernelBound : ℝ := 4096*Real.pi

end
end HigherCorrelations
