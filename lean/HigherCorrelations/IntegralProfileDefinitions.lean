import HigherCorrelations.RationalTransferDefinitions
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Definition-only integral profile and horizontal derivatives. UNCONDITIONAL.
The positive anchor center gives the scalar argument -g in the third factor. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def scalarKernel (x e : ℝ) : ℂ := (1 + ((x : ℂ) + Complex.I * e)^2)⁻¹

def profileIntegrand (a b e f g t : ℝ) : ℂ :=
  scalarKernel (t-a) e * scalarKernel (t-b) f * scalarKernel t (-g)

def integralProfile (a b e f g : ℝ) : ℂ := ∫ t : ℝ, profileIntegrand a b e f g t

def scalarKernelJet (n : ℕ) (x e : ℝ) : ℂ :=
  ((-Complex.I)^n * (n.factorial : ℂ) / (2 * Complex.I)) *
    ((((x : ℂ) + Complex.I * e - Complex.I)⁻¹)^(n+1) -
     (((x : ℂ) + Complex.I * e + Complex.I)⁻¹)^(n+1))

def horizontalPartial : List (Fin 3) → ((Fin 3 → ℝ) → ℂ) → (Fin 3 → ℝ) → ℂ
  | [], F => F
  | j :: js, F => fun δ => fderiv ℝ (horizontalPartial js F) δ (Pi.single j 1)

def horizontalProfile (a b : ℝ) (δ : Fin 3 → ℝ) : ℂ :=
  rationalProfile a b (δ 0) (δ 1) (δ 2)

def profileDerivativeBound (n : ℕ) : ℝ := 4^(n+3) * n.factorial * Real.pi

def profileCenters (a b e f g : ℝ) : Fin 3 → ℂ :=
  ![(a : ℂ)-Complex.I*e, (b : ℂ)-Complex.I*f, Complex.I*g]

def profilePole (z : Fin 3 → ℂ) (i : Fin 3 × Bool) : ℂ :=
  z i.1 + if i.2 then Complex.I else -Complex.I

def poleCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℂ) (i : ι) : ℂ :=
  (∏ j ∈ Finset.univ.erase i, (p i-p j))⁻¹

/-- Ordered mixed partial integrand; the anchor contributes one minus sign per derivative. -/
def profileJetIntegrand (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ) (t : ℝ) : ℂ :=
  scalarKernelJet (js.count 0) (t-a) (δ 0) *
  scalarKernelJet (js.count 1) (t-b) (δ 1) *
  ((-1 : ℂ)^(js.count 2) * scalarKernelJet (js.count 2) t (-δ 2))

def profileJet (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ) : ℂ :=
  ∫ t : ℝ, profileJetIntegrand js a b δ t

def profileJetDifferential (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ) (t : ℝ) :
    (Fin 3 → ℝ) →L[ℝ] ℂ :=
  ∑ j : Fin 3, (ContinuousLinearMap.proj j).smulRight (profileJetIntegrand (j::js) a b δ t)

def profileDirectionalJet : ℕ → List (Fin 3) → ℝ → ℝ → (Fin 3 → ℝ) → ℝ → ℂ
  | 0, js, a, b, δ, s => profileJet js a b (s • δ)
  | n+1, js, a, b, δ, s => ∑ j : Fin 3, (δ j : ℂ) * profileDirectionalJet n (j::js) a b δ s

def profileRay (a b : ℝ) (δ : Fin 3 → ℝ) (s : ℝ) : ℂ := horizontalProfile a b (s • δ)

def horizontalSize (δ : Fin 3 → ℝ) : ℝ := ∑ j, |δ j|

def actualProfileParameters (t : Fin 3 → ZeroOccurrence) : Fin 3 → ℝ :=
  ![occurrenceDisplacement (t 1), occurrenceDisplacement (t 2), occurrenceDisplacement (t 0)]

def actualProfileGap (t : Fin 3 → ZeroOccurrence) (j : Fin 3) : ℝ :=
  occurrenceOrdinate (t j) - occurrenceOrdinate (t 0)

end
end HigherCorrelations
