import HigherCorrelations.IntegralProfileDefinitions
import Mathlib.Analysis.Calculus.Taylor

/-! Definition-only Comparator specifications. Intentional unfinished proofs;
solution modules never import this file. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology

theorem scalar_denominator_lower (x e : ℝ) (he : |e| ≤ 3/4) :
    (7/16 : ℝ) * (1+x^2) ≤ ‖1 + ((x : ℂ) + Complex.I * e)^2‖ := by sorry

theorem scalar_denominator_ne_zero (x e : ℝ) (he : |e| ≤ 3/4) :
    1 + ((x : ℂ) + Complex.I * e)^2 ≠ 0 := by sorry

theorem scalarKernel_bound (x e : ℝ) (he : |e| ≤ 3/4) :
    ‖scalarKernel x e‖ ≤ 4 / (1+x^2) := by sorry

theorem scalarKernel_continuous (e : ℝ) (he : |e| ≤ 3/4) : Continuous (fun x => scalarKernel x e) := by sorry

theorem scalarKernel_integrable (e : ℝ) (he : |e| ≤ 3/4) : Integrable (fun x => scalarKernel x e) := by sorry

theorem profileIntegrand_bound (a b e f g t : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    ‖profileIntegrand a b e f g t‖ ≤ 64 / (1+t^2) := by sorry

theorem profileIntegrand_integrable (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    Integrable (profileIntegrand a b e f g) := by sorry

theorem scalar_poles_ne_zero (x e : ℝ) (he : |e| ≤ 3/4) :
    (x : ℂ) + Complex.I*e - Complex.I ≠ 0 ∧
    (x : ℂ) + Complex.I*e + Complex.I ≠ 0 := by sorry

theorem scalarKernelJet_zero (x e : ℝ) (he : |e| ≤ 3/4) :
    scalarKernelJet 0 x e = scalarKernel x e := by sorry

theorem scalarKernelJet_hasDerivAt (n : ℕ) (x e : ℝ) (he : |e| ≤ 3/4) :
    HasDerivAt (scalarKernelJet n x) (scalarKernelJet (n+1) x e) e := by sorry

theorem shifted_inverse_bounds (x y : ℝ) (hy : 1/4 ≤ |y|) :
    ‖((x : ℂ)+Complex.I*y)⁻¹‖ ≤ 4 ∧
    ‖((x : ℂ)+Complex.I*y)⁻¹‖^2 ≤ 16/(1+x^2) := by sorry

theorem shifted_inverse_power_bound (n : ℕ) (x y : ℝ) (hy : 1/4 ≤ |y|) :
    ‖(((x : ℂ)+Complex.I*y)⁻¹)^(n+2)‖ ≤ 4^(n+2)/(1+x^2) := by sorry

theorem scalarKernelJet_bound (n : ℕ) (x e : ℝ) (he : |e| ≤ 3/4) :
    ‖scalarKernelJet n x e‖ ≤ 4^(n+1) * n.factorial / (1+x^2) := by sorry

theorem simple_pole_partial_fractions {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℂ) (hp : Function.Injective p) (z : ℂ) (hz : ∀ i, z ≠ p i) :
    (∏ i, (z-p i))⁻¹ = ∑ i, (∏ j ∈ Finset.univ.erase i, (p i-p j))⁻¹ / (z-p i) := by sorry

theorem simple_pole_interval (p : ℂ) (hp : p.im ≠ 0) (u v : ℝ) :
    (∫ x : ℝ in u..v, ((x : ℂ)-p)⁻¹) =
      ((Real.log ((v-p.re)^2+p.im^2) / 2 - Real.log ((u-p.re)^2+p.im^2) / 2 : ℝ) : ℂ) +
      Complex.I * (Real.arctan ((v-p.re)/p.im) - Real.arctan ((u-p.re)/p.im)) := by sorry

theorem quadratic_ratio_limit (a y : ℝ) :
    Tendsto (fun R : ℝ => ((R-a)^2+y^2)/((-R-a)^2+y^2)) atTop (𝓝 1) := by sorry

theorem quadratic_log_difference_limit (a y : ℝ) (hy : y ≠ 0) :
    Tendsto (fun R : ℝ => Real.log ((R-a)^2+y^2)/2 -
      Real.log ((-R-a)^2+y^2)/2) atTop (𝓝 0) := by sorry

theorem arctan_difference_limit_pos (a y : ℝ) (hy : 0 < y) :
    Tendsto (fun R : ℝ => Real.arctan ((R-a)/y) - Real.arctan ((-R-a)/y))
      atTop (𝓝 Real.pi) := by sorry

theorem arctan_difference_limit_neg (a y : ℝ) (hy : y < 0) :
    Tendsto (fun R : ℝ => Real.arctan ((R-a)/y) - Real.arctan ((-R-a)/y))
      atTop (𝓝 (-Real.pi)) := by sorry

theorem simple_pole_truncation_upper (p : ℂ) (hp : 0 < p.im) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, ((x : ℂ)-p)⁻¹)
      atTop (𝓝 (Complex.I * Real.pi)) := by sorry

theorem simple_pole_truncation_lower (p : ℂ) (hp : p.im < 0) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, ((x : ℂ)-p)⁻¹)
      atTop (𝓝 (-Complex.I * Real.pi)) := by sorry

theorem finite_poles_truncation {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℂ) (hp : Function.Injective p) (hs : ∀ i, (p i).im ≠ 0) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, (∏ i, ((x : ℂ)-p i))⁻¹) atTop
      (𝓝 (∑ i, poleCoefficient p i * (if 0 < (p i).im then Complex.I*Real.pi else -Complex.I*Real.pi))) := by sorry

theorem profilePole_upper (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 3) :
    0 < (profilePole z (i,true)).im := by sorry

theorem profilePole_lower (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4) (i : Fin 3) :
    (profilePole z (i,false)).im < 0 := by sorry

theorem profilePole_injective (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) : Function.Injective (profilePole z) := by sorry

theorem profilePole_product (z : Fin 3 → ℂ) (v : ℂ) :
    (∏ i : Fin 3 × Bool, (v-profilePole z i)) =
      (1+(v-z 0)^2)*(1+(v-z 1)^2)*(1+(v-z 2)^2) := by sorry

theorem profileCenters_bound (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    ∀ i, |(profileCenters a b e f g i).im| ≤ 3/4 := by sorry

theorem profileCenters_injective (a b e f g : ℝ)
    (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (profileCenters a b e f g) := by sorry

theorem profileIntegrand_eq_poles (a b e f g t : ℝ) :
    profileIntegrand a b e f g t =
      (∏ i : Fin 3 × Bool, ((t : ℂ)-profilePole (profileCenters a b e f g) i))⁻¹ := by sorry

theorem profilePole_coefficient_upper (z : Fin 3 → ℂ) (i : Fin 3) :
    poleCoefficient (profilePole z) (i,true) =
      (2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹ := by sorry

theorem profilePole_coefficient_lower (z : Fin 3 → ℂ) (i : Fin 3) :
    poleCoefficient (profilePole z) (i,false) =
      (-2*Complex.I * ∏ j ∈ Finset.univ.erase i, ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹ := by sorry

theorem quadratic_factor (z : ℂ) : 4+z^2 = (z+2*Complex.I)*(z-2*Complex.I) := by sorry

theorem three_upper_fraction_identity (A B : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : A-B ≠ 0)
    (hAp : A+2*Complex.I ≠ 0) (hAm : A-2*Complex.I ≠ 0)
    (hBp : B+2*Complex.I ≠ 0) (hBm : B-2*Complex.I ≠ 0)
    (hDp : A-B+2*Complex.I ≠ 0) (hDm : A-B-2*Complex.I ≠ 0) :
    1 / ((A-B)*(A-B+2*Complex.I)*A*(A+2*Complex.I)) +
    1 / ((-(A-B))*(-(A-B)+2*Complex.I)*B*(B+2*Complex.I)) +
    1 / ((-A)*(-A+2*Complex.I)*(-B)*(-B+2*Complex.I)) =
      (24+(A-B)^2+A^2+B^2)/((4+(A-B)^2)*(4+A^2)*(4+B^2)) := by sorry

theorem center_difference_shifts_ne (z w : ℂ) (hz : |z.im| ≤ 3/4) (hw : |w.im| ≤ 3/4) :
    z-w+2*Complex.I ≠ 0 ∧ z-w-2*Complex.I ≠ 0 := by sorry

theorem center_quadratic_ne (z w : ℂ) (hz : |z.im| ≤ 3/4) (hw : |w.im| ≤ 3/4) :
    4+(z-w)^2 ≠ 0 := by sorry

theorem upper_center_sum (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j+2*Complex.I)))⁻¹) = rationalKernel (z 0) (z 1) (z 2) := by sorry

theorem lower_center_sum (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (Real.pi : ℂ) * (∑ i, (∏ j ∈ Finset.univ.erase i,
      ((z i-z j)*(z i-z j-2*Complex.I)))⁻¹) = rationalKernel (z 0) (z 1) (z 2) := by sorry

theorem profile_pole_sum (z : Fin 3 → ℂ) (hz : ∀ i, |(z i).im| ≤ 3/4)
    (hinj : Function.Injective z) :
    (∑ i : Fin 3 × Bool, poleCoefficient (profilePole z) i *
      (if 0 < (profilePole z i).im then Complex.I*Real.pi else -Complex.I*Real.pi)) =
      rationalKernel (z 0) (z 1) (z 2) := by sorry

theorem integralProfile_eq_of_distinct (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4)
    (hab : a ≠ b) (ha : a ≠ 0) (hb : b ≠ 0) :
    integralProfile a b e f g = rationalProfile a b e f g := by sorry

theorem integralProfile_continuous_gaps (e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    Continuous (fun p : ℝ × ℝ => integralProfile p.1 p.2 e f g) := by sorry

theorem rationalProfile_continuous_gaps (e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    Continuous (fun p : ℝ × ℝ => rationalProfile p.1 p.2 e f g) := by sorry

theorem integralProfile_eq (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    integralProfile a b e f g = rationalProfile a b e f g := by sorry

theorem profile_counts_sum (js : List (Fin 3)) :
    js.count 0 + js.count 1 + js.count 2 = js.length := by sorry

theorem profile_counts_factorial (js : List (Fin 3)) :
    (js.count 0).factorial * (js.count 1).factorial * (js.count 2).factorial ≤ js.length.factorial := by sorry

theorem profileJetIntegrand_bound (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ) (t : ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) :
    ‖profileJetIntegrand js a b δ t‖ ≤ (4^(js.length+3)*js.length.factorial) / (1+t^2) := by sorry

theorem scalarKernelJet_continuous_x (n : ℕ) (e : ℝ) (he : |e| ≤ 3/4) :
    Continuous (fun x => scalarKernelJet n x e) := by sorry

theorem profileJetIntegrand_continuous (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) : Continuous (profileJetIntegrand js a b δ) := by sorry

theorem profileJetIntegrand_integrable (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) : Integrable (profileJetIntegrand js a b δ) := by sorry

theorem profileJet_bound (js : List (Fin 3)) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 3/4) : ‖profileJet js a b δ‖ ≤ profileDerivativeBound js.length := by sorry

theorem scalarKernelJet_hasFDerivAt_coordinate (n : ℕ) (x : ℝ) (δ : Fin 3 → ℝ)
    (j : Fin 3) (hj : |δ j| ≤ 3/4) :
    HasFDerivAt (𝕜 := ℝ) (fun η : Fin 3 → ℝ => scalarKernelJet n x (η j))
      ((ContinuousLinearMap.proj j).smulRight (scalarKernelJet (n+1) x (δ j))) δ := by sorry

theorem profileJetIntegrand_hasFDerivAt (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (t : ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    HasFDerivAt (𝕜 := ℝ) (fun η => profileJetIntegrand js a b η t)
      (profileJetDifferential js a b δ t) δ := by sorry

theorem profileJetDifferential_continuous (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    Continuous (profileJetDifferential js a b δ) := by sorry

theorem profileJetDifferential_bound (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (t : ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    ‖profileJetDifferential js a b δ t‖ ≤
      3*(4^(js.length+4)*(js.length+1).factorial)/(1+t^2) := by sorry

theorem profileJetDifferential_integrable (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 3/4) :
    Integrable (profileJetDifferential js a b δ) := by sorry

theorem horizontal_cube_mem_nhds (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    {η : Fin 3 → ℝ | ∀ j, |η j| < 3/4} ∈ 𝓝 δ := by sorry

theorem profileJet_hasFDerivAt (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    HasFDerivAt (profileJet js a b) (∫ t : ℝ, profileJetDifferential js a b δ t) δ := by sorry

theorem profileJet_fderiv_coordinate (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (j : Fin 3) (hδ : ∀ j, |δ j| < 3/4) :
    fderiv ℝ (profileJet js a b) δ (Pi.single j 1) = profileJet (j::js) a b δ := by sorry

theorem horizontalPartial_eq_profileJet (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    horizontalPartial js (horizontalProfile a b) δ = profileJet js a b δ := by sorry

theorem horizontalPartial_bound (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖horizontalPartial js (horizontalProfile a b) δ‖ ≤ profileDerivativeBound js.length := by sorry

theorem rationalProfile_contDiffAt (p : Fin 5 → ℝ)
    (he : |p 2| ≤ 3/4) (hf : |p 3| ≤ 3/4) (hg : |p 4| ≤ 3/4) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => rationalProfile (q 0) (q 1) (q 2) (q 3) (q 4)) p := by sorry

theorem profileRay_contDiffAt (a b : ℝ) (δ : Fin 3 → ℝ) (s : ℝ)
    (hs : ∀ j, |s*δ j| ≤ 3/4) : ContDiffAt ℝ ⊤ (profileRay a b δ) s := by sorry

theorem integralProfile_contDiffAt (p : Fin 5 → ℝ)
    (he : |p 2| ≤ 1/2) (hf : |p 3| ≤ 1/2) (hg : |p 4| ≤ 1/2) :
    ContDiffAt ℝ ⊤ (fun q : Fin 5 → ℝ => integralProfile (q 0) (q 1) (q 2) (q 3) (q 4)) p := by sorry

theorem profileJet_fderiv_apply (js : List (Fin 3)) (a b : ℝ)
    (δ v : Fin 3 → ℝ) (hδ : ∀ j, |δ j| < 3/4) :
    fderiv ℝ (profileJet js a b) δ v = ∑ j, (v j : ℂ)*profileJet (j::js) a b δ := by sorry

theorem profileDirectionalJet_hasDerivAt (n : ℕ) (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (s : ℝ) (hs : ∀ j, |s*δ j| < 3/4) :
    HasDerivAt (profileDirectionalJet n js a b δ)
      (profileDirectionalJet (n+1) js a b δ s) s := by sorry

theorem profileDirectionalJet_bound (n : ℕ) (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) (s : ℝ) (hs : ∀ j, |s*δ j| ≤ 3/4) :
    ‖profileDirectionalJet n js a b δ s‖ ≤
      profileDerivativeBound (n+js.length) * horizontalSize δ ^ n := by sorry

theorem profile_ray_cube_mem_nhds (δ : Fin 3 → ℝ) (s : ℝ) (hs : ∀ j, |s*δ j| < 3/4) :
    {t : ℝ | ∀ j, |t*δ j| < 3/4} ∈ 𝓝 s := by sorry

theorem profileRay_iteratedDeriv (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ) (s : ℝ)
    (hs : ∀ j, |s*δ j| < 3/4) :
    iteratedDeriv n (profileRay a b δ) s = profileDirectionalJet n [] a b δ s := by sorry

theorem profileRay_derivative_bound (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ) (s : ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) (hs : |s| ≤ 1) :
    ‖iteratedDeriv n (profileRay a b δ) s‖ ≤ profileDerivativeBound n * horizontalSize δ ^ n := by sorry

theorem profileRay_contDiffOn (a b : ℝ) (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    ContDiffOn ℝ ⊤ (profileRay a b δ) (Set.Icc (0 : ℝ) 1) := by sorry

theorem profileRay_iteratedDerivWithin (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin n (profileRay a b δ) (Set.Icc 0 1) s =
      iteratedDeriv n (profileRay a b δ) s := by sorry

theorem profile_taylor_remainder_bound (n : ℕ) (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖profileRay a b δ 1 - taylorWithinEval (profileRay a b δ) n (Set.Icc 0 1) 0 1‖ ≤
      profileDerivativeBound (n+1) * horizontalSize δ ^ (n+1) / (n+1).factorial := by sorry

theorem profileDirectionalJet_neg_at_zero (n : ℕ) (js : List (Fin 3)) (a b : ℝ)
    (δ : Fin 3 → ℝ) : profileDirectionalJet n js a b (-δ) 0 =
      (-1 : ℂ)^n * profileDirectionalJet n js a b δ 0 := by sorry

theorem profileTaylor_one (a b : ℝ) (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    taylorWithinEval (profileRay a b δ) 1 (Set.Icc 0 1) 0 1 =
      horizontalProfile a b 0 + profileDirectionalJet 1 [] a b δ 0 := by sorry

theorem profileTaylor_three (a b : ℝ) (δ : Fin 3 → ℝ) (hδ : ∀ j, |δ j| ≤ 1/2) :
    taylorWithinEval (profileRay a b δ) 3 (Set.Icc 0 1) 0 1 =
      horizontalProfile a b 0 + profileDirectionalJet 1 [] a b δ 0 +
      profileDirectionalJet 2 [] a b δ 0 / 2 + profileDirectionalJet 3 [] a b δ 0 / 6 := by sorry

theorem profile_symmetric_second_bound (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖(horizontalProfile a b δ + horizontalProfile a b (-δ))/2 - horizontalProfile a b 0‖ ≤
      profileDerivativeBound 2 * horizontalSize δ ^ 2 / 2 := by sorry

theorem profile_symmetric_fourth_bound (a b : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖(horizontalProfile a b δ + horizontalProfile a b (-δ))/2 - horizontalProfile a b 0 -
        iteratedDeriv 2 (profileRay a b δ) 0 / 2‖ ≤
      profileDerivativeBound 4 * horizontalSize δ ^ 4 / 24 := by sorry

theorem actualProfileParameters_bound (t : Fin 3 → ZeroOccurrence) :
    ∀ j, |actualProfileParameters t j| ≤ 1/2 := by sorry

theorem actualRationalKernel_integral (t : Fin 3 → ZeroOccurrence) :
    actualRationalKernel t = ∫ v : ℝ,
      profileIntegrand (actualProfileGap t 1) (actualProfileGap t 2)
        (actualProfileParameters t 0) (actualProfileParameters t 1) (actualProfileParameters t 2) v := by sorry

theorem actualProfile_integrable (t : Fin 3 → ZeroOccurrence) :
    Integrable (profileIntegrand (actualProfileGap t 1) (actualProfileGap t 2)
      (actualProfileParameters t 0) (actualProfileParameters t 1) (actualProfileParameters t 2)) := by sorry

theorem actualProfile_horizontal_bound (js : List (Fin 3)) (t : Fin 3 → ZeroOccurrence) :
    ‖horizontalPartial js (horizontalProfile (actualProfileGap t 1) (actualProfileGap t 2))
        (actualProfileParameters t)‖ ≤ profileDerivativeBound js.length := by sorry

theorem actualProfile_symmetric_second (t : Fin 3 → ZeroOccurrence) :
    ‖(actualRationalKernel t + horizontalProfile (actualProfileGap t 1) (actualProfileGap t 2)
        (-actualProfileParameters t))/2 - actualRealKernel t‖ ≤
      profileDerivativeBound 2 * horizontalSize (actualProfileParameters t)^2 / 2 := by sorry

theorem actualProfile_symmetric_fourth (t : Fin 3 → ZeroOccurrence) :
    ‖(actualRationalKernel t + horizontalProfile (actualProfileGap t 1) (actualProfileGap t 2)
        (-actualProfileParameters t))/2 - actualRealKernel t -
      iteratedDeriv 2 (profileRay (actualProfileGap t 1) (actualProfileGap t 2) (actualProfileParameters t)) 0 / 2‖ ≤
      profileDerivativeBound 4 * horizontalSize (actualProfileParameters t)^4 / 24 := by sorry

end
end HigherCorrelations
