import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Definition-only interface for PAIR-MEANVALUE-001. UNCONDITIONAL.
Frequencies are in cycles per unit time. Q counts ordered pairs with a
strict positive gap strictly below delta; injectivity is a theorem hypothesis. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def pairMeanCharacter (u : ℝ) : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I*u)

def pairMeanFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ, pairMeanCharacter (-t*ξ) * f t

def pairFrequencySum {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ) (t : ℝ) : ℂ :=
  ∑' i, c i * pairMeanCharacter (μ i*t)

def pairFrequencyDiagonal {ι : Type*} (c : ι → ℂ) : ℝ := ∑' i, ‖c i‖^2

def pairFrequencyNearby {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ) (δ : ℝ) : ℝ :=
  ∑' p : ι × ι, if 0 < |μ p.1-μ p.2| ∧ |μ p.1-μ p.2| < δ
    then ‖c p.1‖*‖c p.2‖ else 0

def pairMeanSinc (u : ℝ) : ℝ := Real.sinc (Real.pi*u)
def pairMeanTriangle (ξ : ℝ) : ℝ := max 0 (1-|ξ|)
def pairMeanBox (ξ : ℝ) : ℂ := Set.indicator (Set.Icc (-(1/2:ℝ)) (1/2)) (fun _ => 1) ξ
def pairMeanK (u : ℝ) : ℝ := (3/4:ℝ)*pairMeanSinc (u/2)^4
def pairMeanB (u : ℝ) : ℝ := pairMeanSinc (u/2)^2+pairMeanSinc ((u-1)/2)^2
def pairMeanTail (r : ℝ) : ℝ := ∫ u in {u : ℝ | r ≤ |u|}, pairMeanK u
def pairMeanConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u : ℝ, f u*g (t-u)
def pairMeanInterval (T t : ℝ) : ℝ := Set.indicator (Set.Icc 0 T) (fun _ => 1) t
def pairMeanScaledK (δ t : ℝ) : ℝ := δ*pairMeanK (δ*t)
def pairMeanEnvelope (T δ ε t : ℝ) : ℝ :=
  pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t +
    ε*64*(pairMeanB (δ*t)+pairMeanB (δ*(t-T)))

end
end HigherCorrelations
