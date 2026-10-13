import Mathlib.Analysis.MellinTransform

/-! Definition-only interface for the upward paired Mellin kernel.
UNCONDITIONAL. Positive-base powers use exp(w log y), and w=2+t*i
parametrizes the line upward. The Jacobian i is retained in the line integral. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def pairedMellinSeed (x : ℝ) : ℂ :=
  Set.indicator (Set.Ioc 0 1) (fun x : ℝ => (x : ℂ)⁻¹ - x) x

def pairedMellinSymbol (w : ℂ) : ℂ := 2/(w^2-1)

def pairedMellinIntegrand (y t : ℝ) : ℂ :=
  2 * Complex.exp ((2+(t : ℂ)*Complex.I)*(Real.log y : ℂ)) /
    ((2+(t : ℂ)*Complex.I)^2-1)

def pairedMellinKernel (y : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℝ) • ∫ t : ℝ, pairedMellinIntegrand y t

def pairedMellinUpwardIntegral (y : ℝ) : ℂ :=
  (1/(2*(Real.pi : ℂ)*Complex.I)) * ∫ t : ℝ, pairedMellinIntegrand y t * Complex.I

def pairedMellinTruncation (y V : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℝ) • ∫ t in -V..V, pairedMellinIntegrand y t

end
end HigherCorrelations
