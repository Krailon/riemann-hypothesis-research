import HigherCorrelations.TripleArithmeticDefinitions
import HigherCorrelations.TripleBudgetDefinitions
import HigherCorrelations.TripleBudgetInteriorDefinitions
import HigherCorrelations.TripleBudgetUniformDefinitions
import HigherCorrelations.TripleDyadicDefinitions
import HigherCorrelations.TripleLogGapDefinitions
import HigherCorrelations.TripleOffFourierDefinitions

/-! UNCONDITIONAL independent statement surface. Intentional holes belong only to challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleArithmeticCoefficient_succ (x : ℝ) (n : ℕ) :
    tripleArithmeticCoefficient x (n+1) = pairMeanPrimeCoefficient x n := by sorry

theorem tripleArithmeticCoefficient_nonneg (x : ℝ) (hx : 1≤ x) (n : ℕ) :
    0≤ tripleArithmeticCoefficient x n := by sorry

theorem tripleArithmeticCoefficient_zero (x : ℝ) : tripleArithmeticCoefficient x 0 = 0 := by sorry

theorem tripleArithmeticCoefficient_one (x : ℝ) : tripleArithmeticCoefficient x 1 = 0 := by sorry

theorem tripleArithmeticCoefficient_summable (x : ℝ) (hx : 1≤ x) :
    Summable (tripleArithmeticCoefficient x) := by sorry

theorem tripleLogCoefficient_mass_summable (x : ℝ) (hx : 1≤ x) :
    Summable (fun n => ‖tripleLogCoefficient x n‖) := by sorry

theorem tripleLogCoefficient_energy_pointwise (x : ℝ) (hx : 1≤ x) (n : LogGapIndex) :
    tripleLogEnergyTerm (tripleLogCoefficient x) n ≤ tripleDyadicMoment x 3 n.val := by sorry

theorem tripleLogCoefficient_energy_summable (x : ℝ) (hx : 1≤ x) :
    Summable (tripleLogEnergyTerm (tripleLogCoefficient x)) := by sorry

theorem tripleLogCoefficient_energy_bound (x : ℝ) (hx : 1≤ x) :
    tripleLogEnergy (tripleLogCoefficient x) ≤ tripleDyadicConstant 3*x*Real.log (2*x)^3 := by sorry

theorem tripleNat_tsum_ge_two {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : ℕ → E) (h0 : f 0=0) (h1 : f 1=0) :
    (∑' n : LogGapIndex, f n.val) = ∑' n : ℕ, f n := by sorry

theorem tripleArithmetic_phase_summable (x t : ℝ) (hx : 1≤ x) :
    Summable (fun n : ℕ => ‖(tripleArithmeticCoefficient x n:ℂ)*
      pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)‖) := by sorry

theorem tripleArithmetic_phase_sum (x t : ℝ) (hx : 1≤ x) :
    (∑' n : ℕ, (tripleArithmeticCoefficient x n:ℂ)*pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)) =
      pairPrimeSeries (x,t) := by sorry

theorem tripleLogCoefficient_series (x t : ℝ) (hx : 1≤ x) :
    pairFrequencySum tripleLogFrequency (tripleLogCoefficient x) t = pairPrimeSeries (x,t) := by sorry

theorem tripleArithmetic_phase_mul (X Y t : ℝ) (m n : ℕ) :
    ((tripleArithmeticCoefficient X m:ℂ)*pairMeanCharacter ((-Real.log m/(2*Real.pi))*t))*
      ((tripleArithmeticCoefficient Y n:ℂ)*pairMeanCharacter ((-Real.log n/(2*Real.pi))*t)) =
    ((tripleArithmeticCoefficient X m*tripleArithmeticCoefficient Y n:ℝ):ℂ)*
      pairMeanCharacter ((-Real.log (m*n)/(2*Real.pi))*t) := by sorry

theorem tripleArithmeticConvolution_phase_fiber (X Y t : ℝ) (r : ℕ) :
    (∑' p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r},
      ((tripleArithmeticCoefficient X p.val.1:ℂ)*pairMeanCharacter ((-Real.log p.val.1/(2*Real.pi))*t))*
        ((tripleArithmeticCoefficient Y p.val.2:ℂ)*pairMeanCharacter ((-Real.log p.val.2/(2*Real.pi))*t))) =
    (tripleArithmeticConvolution X Y r:ℂ)*pairMeanCharacter ((-Real.log r/(2*Real.pi))*t) := by sorry

theorem tripleArithmeticConvolution_phase_sum (X Y t : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    (∑' r : ℕ, (tripleArithmeticConvolution X Y r:ℂ)*pairMeanCharacter ((-Real.log r/(2*Real.pi))*t)) =
      pairPrimeSeries (X,t)*pairPrimeSeries (Y,t) := by sorry

theorem tripleLogConvolution_series (X Y t : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    pairFrequencySum tripleLogFrequency (tripleLogConvolution X Y) t =
      pairPrimeSeries (X,t)*pairPrimeSeries (Y,t) := by sorry

theorem tripleLogCoefficient_mass_bound (x : ℝ) (hx : 1≤ x) :
    tripleLogMass (tripleLogCoefficient x) ≤ triplePrimeMass x := by sorry

theorem tripleLogGapBound_mono (c d : LogGapIndex → ℂ) (B C E F : ℝ)
    (hb : tripleLogMass c≤ B) (hc : tripleLogMass d≤ C)
    (he : tripleLogEnergy c≤ E) (hf : tripleLogEnergy d≤ F) :
    tripleLogGapBound c d ≤ B*C/Real.log 2 +4*Real.sqrt 2*Real.sqrt (E*F) := by sorry

theorem tripleLogGap_mixed_budget (x y : ℝ) (hx : 1≤ x) (hy : 1≤ y) :
    tripleLogGapBound (tripleLogCoefficient x) (tripleLogCoefficient y) ≤
      (triplePrimeMassConstant*Real.sqrt x*Real.log (2*x))*
        (triplePrimeMassConstant*Real.sqrt y*Real.log (2*y))/Real.log 2 +
      4*Real.sqrt 2*Real.sqrt ((tripleDyadicConstant 3*x*Real.log (2*x)^3)*
        (tripleDyadicConstant 3*y*Real.log (2*y)^3)) := by sorry

theorem tripleLogGap_cubic_budget (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleLogGapBound (tripleLogConvolution X Y) (tripleLogCoefficient (X*Y)) ≤
      ((triplePrimeMassConstant*Real.sqrt X*Real.log (2*X))*
        (triplePrimeMassConstant*Real.sqrt Y*Real.log (2*Y)))*
        (triplePrimeMassConstant*Real.sqrt (X*Y)*Real.log (2*(X*Y)))/Real.log 2 +
      4*Real.sqrt 2*Real.sqrt ((tripleDyadicConstant 5*(X*Y)*Real.log (2*(X*Y))^5)*
        (tripleDyadicConstant 3*(X*Y)*Real.log (2*(X*Y))^3)) := by sorry

theorem tripleBudgetWeight_support (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    Function.support ω ⊆ Icc (1:ℝ) 2 := by sorry

theorem tripleBudgetMoment_scale (ω : ℝ → ℝ) (T : ℝ) (hT : 0< T) (r : ℕ) :
    (∫ t : ℝ, ω (t/T)/T * Real.log (|t|+2)^r) = tripleBudgetMoment ω T r := by sorry

theorem tripleBudgetMoment_manuscript (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤ T) (r : ℕ) :
    tripleBudgetMoment ω T r = ∫ u in Ioo (1:ℝ) 2, ω u*Real.log (T*u+2)^r := by sorry

theorem tripleBudget_AAA (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0< T) :
    tripleWordIntegral ω T X Y ![.A,.A,.A] =
      (tripleBudgetMoment ω T 3/(X*Y)^2 : ℝ) := by sorry

theorem tripleBudget_remainder_count : tripleBudgetRemainderWords.card = 19 := by sorry

theorem tripleBudget_refinement_count :
    (∑ w ∈ tripleBudgetRemainderWords, Fintype.card (TripleBudgetAssignment w)) = 208 := by sorry

theorem tripleBudget_exact (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleMasterObservable ω T X Y = tripleBudgetRetained ω T X Y +
      (∑ e : TripleBudgetError, tripleBudgetError ω T X Y e) +
      ∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w := by sorry

theorem tripleBudget_PPPoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleBudgetError ω T X Y .PPPoff = -triplePrimeOffSeries ω T X Y := by sorry

theorem tripleBudget_uniform_lower_scale : ∃ C : ℝ, 0< C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T R X Y : ℝ,
      0≤ W → (∀ u, ω u≤ W) → 3≤ T → 1≤ R → R≤ X → R≤ Y → X*Y≤ T/R →
        ‖tripleMasterObservable ω T X Y-tripleBudgetRetained ω T X Y‖ ≤
          C*(1+W+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by sorry

theorem tripleBudget_uniform_asymptotic : ∃ C : ℝ, 0< C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W ε T X Y : ℝ,
      0≤ W → (∀ u, ω u≤ W) → 0<ε → ε<1/3 → 3≤ T →
      T^ε≤ X → T^ε≤ Y → X*Y≤ T^(1-ε) →
        ‖tripleMasterObservable ω T X Y-tripleBudgetRetained ω T X Y‖ ≤
          C*tripleBudgetEnvelope ε W (fourierDerivativeL1 ω 1) T := by sorry

theorem tripleBudget_uniform_additive_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (W ε : ℝ) (hW : 0≤ W) (hωW : ∀ u, ω u≤ W) (hε : 0<ε) (hεupper : ε<1/3) :
    ∀ η : ℝ, 0<η → ∀ᶠ T : ℝ in atTop, ∀ X Y : ℝ,
      T^ε≤ X → T^ε≤ Y → X*Y≤ T^(1-ε) →
        ‖tripleMasterObservable ω T X Y-tripleBudgetRetained ω T X Y‖<η := by sorry

theorem tripleBudget_PAPoff_coarse (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PAPoff‖ ≤ tripleBudgetAlpha T Y*
      (tripleBudgetPrimeL2 ω T X*tripleBudgetPrimeL2 ω T (X*Y)+tripleBudgetDiagonal X (X*Y)) := by sorry

theorem tripleBudget_APPoff_swap (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleBudgetError ω T X Y .APPoff = tripleBudgetError ω T Y X .PAPoff := by sorry

theorem tripleBudget_APPoff_coarse (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .APPoff‖ ≤ tripleBudgetAlpha T X*
      (tripleBudgetPrimeL2 ω T Y*tripleBudgetPrimeL2 ω T (X*Y)+tripleBudgetDiagonal Y (X*Y)) := by sorry

theorem tripleBudget_PPP_coarse (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleWordIntegral ω T X Y ![.P,.P,.P]‖ ≤
      min (min (triplePrimeMass X*tripleBudgetPrimeL2 ω T Y*tripleBudgetPrimeL2 ω T (X*Y))
        (triplePrimeMass Y*tripleBudgetPrimeL2 ω T X*tripleBudgetPrimeL2 ω T (X*Y)))
        (triplePrimeMass (X*Y)*tripleBudgetPrimeL2 ω T X*tripleBudgetPrimeL2 ω T Y) := by sorry

theorem tripleBudgetDiagonal_summable (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    Summable (fun n : ℕ => pairMeanPrimeCoefficient X n*pairMeanPrimeCoefficient Y n) := by sorry

theorem tripleBudgetDiagonal_nonneg (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    0 ≤ tripleBudgetDiagonal X Y := by sorry

theorem tripleBudgetDiagonal_swap (X Y : ℝ) :
    tripleBudgetDiagonal X Y = tripleBudgetDiagonal Y X := by sorry

theorem tripleBudgetDiagonal_self (X : ℝ) :
    tripleBudgetDiagonal X X = pairMeanPrimeDiagonal X := by sorry

theorem tripleBudgetDiagonal_cauchy (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleBudgetDiagonal X Y ≤
      Real.sqrt (pairMeanPrimeDiagonal X)*Real.sqrt (pairMeanPrimeDiagonal Y) := by sorry

theorem tripleBudgetDiagonal_uniform : ∃ C : ℝ, 0< C ∧ ∀ X Y : ℝ,
    1≤ X → 1≤ Y → tripleBudgetDiagonal X Y ≤ C*Real.sqrt (Real.log (2*X)*Real.log (2*Y)) := by sorry

theorem tripleBudgetOmega_height (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) :
    tripleBudgetOmega ω T 1 ≤ (1+fourierDerivativeL1 ω 1)*Real.log (2*T+2) ∧
    tripleBudgetOmega ω T 2 ≤ 2*(1+fourierDerivativeL1 ω 1)*Real.log (2*T+2)^2 := by sorry

theorem tripleBudget_coefficient_log_height (T x : ℝ) (hT : 3≤ T) (hx : 1≤ x) (hxT : x≤ T) :
    0≤ Real.log (2*x) ∧ Real.log (2*x)≤ Real.log (2*T+2) := by sorry

theorem tripleBudget_mixed_log_height (T x y : ℝ) (hT : 3≤ T)
    (hx : 1≤ x) (hy : 1≤ y) (hxT : x≤ T) (hyT : y≤ T) :
    Real.sqrt (Real.log (2*x)^3*Real.log (2*y)^3)≤ Real.log (2*T+2)^3 := by sorry

theorem tripleBudget_mass_pair_height (T X Y : ℝ) (hT : 3≤ T)
    (hX : 1≤ X) (hY : 1≤ Y) (hXT : X≤ T) (hYT : Y≤ T) :
    triplePrimeMass X*triplePrimeMass Y/(X*Y) ≤ triplePrimeMassConstant^2*Real.log (2*T+2)^2 := by sorry

theorem tripleBudget_single_words_height (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PAA‖ ≤ 5*tripleBudgetOmega ω T 2/T ∧
    ‖tripleBudgetError ω T X Y .APA‖ ≤ 5*tripleBudgetOmega ω T 2/T ∧
    ‖tripleBudgetError ω T X Y .AAP‖ ≤ 5*tripleBudgetOmega ω T 2/T := by sorry

theorem tripleBudget_archConstant_nonneg : 0≤ pairArchConstant := by sorry

theorem tripleBudgetHConstant_pos : 0< tripleBudgetHConstant := by sorry

theorem tripleBudget_height_log (T : ℝ) (hT : 3≤ T) : 1≤ Real.log (2*T+2) := by sorry

theorem tripleBudget_remainder_interior (T R x : ℝ) (hT : 3≤ T)
    (hR : 1≤ R) (hxR : R≤ x) (hxT : x≤ T) :
    tripleBudgetRemainderTotal T x ≤ tripleBudgetHConstant/R := by sorry

theorem tripleBudget_letter_interior (C : ℝ) (hC : 0< C)
    (hmean : ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T x : ℝ,
      0≤ W → (∀ u, ω u≤ W) → 3≤ T → 1≤ x → x≤ 2*T →
        tripleBudgetPrimeL2 ω T x≤ Real.sqrt (2*C*W*Real.log (2*x)))
    (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) (W T R x : ℝ)
    (hW : 0≤ W) (hωW : ∀ u, ω u≤ W) (hT : 3≤ T) (hR : 1≤ R) (hxR : R≤ x) (hxT : x≤ T)
    (l : MasterLetter) :
    tripleBudgetLetterNorm ω T x l ≤
      tripleBudgetInteriorNormConstant C*Real.sqrt (1+W)*Real.log (2*T+2) := by sorry

theorem tripleBudget_range_geometry (T R X Y : ℝ) (hT : 3≤ T) (hR : 1≤ R)
    (hX : R≤ X) (hY : R≤ Y) (hZ : X*Y≤ T/R) :
    (R≤ X*Y) ∧ X≤ T ∧ Y≤ T ∧ X*Y≤ T := by sorry

theorem tripleBudget_remainder_words_uniform : ∃ K : ℝ, 0< K ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T R X Y : ℝ,
      0≤ W → (∀ u, ω u≤ W) → 3≤ T → 1≤ R → R≤ X → R≤ Y → X*Y≤ T/R →
        ‖∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w‖ ≤
          K*(1+W)/R*Real.log (2*T+2)^2 := by sorry

theorem tripleBudget_weight_mass (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) : (∫ t : ℝ, ω (t/T)/T) = 1 := by sorry

theorem tripleBudget_weighted_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun t => ω (t/T)/T*f t) := by sorry

theorem tripleBudget_sqrt_weight_memLp (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp (fun t => Real.sqrt (ω (t/T)/T)*‖f t‖) 2 := by sorry

theorem tripleBudgetL2_cauchy (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ t : ℝ, ω (t/T)/T*‖f t‖*‖g t‖) ≤ tripleBudgetL2 ω T f*tripleBudgetL2 ω T g := by sorry

theorem tripleBudgetL2_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f : ℝ → ℂ) (hf : Continuous f) (B : ℝ) (hB : 0≤ B)
    (hb : ∀ t ∈ Icc T (2*T), ‖f t‖≤ B) : tripleBudgetL2 ω T f ≤ B := by sorry

theorem tripleBudget_integral_norm_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f g h : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (B : ℝ) (hB : 0≤ B) (hb : ∀ t ∈ Icc T (2*T), ‖h t‖≤ B) :
    ‖tripleSmoothedIntegral ω T f g h‖ ≤ tripleBudgetL2 ω T f*tripleBudgetL2 ω T g*B := by sorry

theorem tripleBudget_log_height (T : ℝ) (hT : 3≤ T) :
    0≤ Real.log (2*T+2) ∧ Real.log (2*T+2) ≤ 2*Real.log T := by sorry

theorem tripleBudgetEnvelope_bound (ε Winf W₁ T : ℝ) (hW : 0≤ Winf) (hW₁ : 0≤ W₁) (hT : 3≤ T) :
    0≤ tripleBudgetEnvelope ε Winf W₁ T ∧
      tripleBudgetEnvelope ε Winf W₁ T ≤
        (16*(1+Winf+W₁))*(Real.log T^4/T^ε) := by sorry

theorem tripleBudgetEnvelope_tendsto (ε Winf W₁ : ℝ) (hε : 0<ε) (hW : 0≤ Winf) (hW₁ : 0≤ W₁) :
    Tendsto (tripleBudgetEnvelope ε Winf W₁) atTop (𝓝 0) := by sorry

theorem tripleBudgetLogWeight_support (ω : ℝ → ℝ) (T : ℝ) (r : ℕ) :
    tsupport (tripleBudgetLogWeight ω T r) ⊆ tsupport ω := by sorry

theorem tripleBudgetLogWeight_smooth (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) (r : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (tripleBudgetLogWeight ω T r) := by sorry

theorem tripleBudgetLogWeight_compact (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (r : ℕ) : HasCompactSupport (tripleBudgetLogWeight ω T r) := by sorry

theorem tripleBudgetLogWeight_deriv (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) (r : ℕ) (u : ℝ) (hu : u∈tsupport ω) :
    deriv (tripleBudgetLogWeight ω T r) u =
      deriv ω u*Real.log (T*u+2)^r + ω u*((r:ℝ)*Real.log (T*u+2)^(r-1)*(T/(T*u+2))) := by sorry

theorem tripleBudgetLogWeight_deriv_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) (r : ℕ) (u : ℝ) :
    |deriv (tripleBudgetLogWeight ω T r) u| ≤
      |deriv ω u| *Real.log (2*T+2)^r + ω u*((r:ℝ)*Real.log (2*T+2)^(r-1)) := by sorry

theorem tripleBudgetOmega_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) (r : ℕ) :
    tripleBudgetOmega ω T r ≤ fourierDerivativeL1 ω 1*Real.log (2*T+2)^r + (r:ℝ)*Real.log (2*T+2)^(r-1) := by sorry

theorem tripleBudget_PPA_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0< T) :
    tripleBudgetError ω T X Y .PPA = (1/((X*Y:ℝ):ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 1 (t/T)/T:ℝ):ℂ)*(pairPrimeSeries (X,t)*pairPrimeSeries (Y,t)) := by sorry

theorem tripleBudget_PAA_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0< T) :
    tripleBudgetError ω T X Y .PAA = -(1/((Y*(X*Y):ℝ):ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 2 (t/T)/T:ℝ):ℂ)*pairPrimeSeries (X,t) := by sorry

theorem tripleBudget_APA_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0< T) :
    tripleBudgetError ω T X Y .APA = -(1/((X*(X*Y):ℝ):ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 2 (t/T)/T:ℝ):ℂ)*pairPrimeSeries (Y,t) := by sorry

theorem tripleBudget_AAP_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0< T) :
    tripleBudgetError ω T X Y .AAP = -(1/((X*Y:ℝ):ℂ))*star
      (∫ t, ((tripleBudgetLogWeight ω T 2 (t/T)/T:ℝ):ℂ)*pairPrimeSeries (X*Y,t)) := by sorry

theorem tripleBudget_PPA_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PPA‖ ≤
      triplePrimeMass X*triplePrimeMass Y*tripleBudgetOmega ω T 1/((X*Y)*T*Real.log 4) := by sorry

theorem tripleBudget_PAA_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PAA‖ ≤ 5*Real.sqrt X*tripleBudgetOmega ω T 2/(T*Y*(X*Y)) := by sorry

theorem tripleBudget_APA_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .APA‖ ≤ 5*Real.sqrt Y*tripleBudgetOmega ω T 2/(T*X*(X*Y)) := by sorry

theorem tripleBudget_AAP_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .AAP‖ ≤ 5*Real.sqrt (X*Y)*tripleBudgetOmega ω T 2/(T*X*Y) := by sorry

theorem tripleLogCoefficient_diagonal (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    (∑' n : LogGapIndex, tripleLogCoefficient X n*star (tripleLogCoefficient Y n)) =
      (tripleBudgetDiagonal X Y:ℂ) := by sorry

theorem tripleBudgetLogWeight_scaled (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (r : ℕ) (t : ℝ) :
    tripleBudgetLogWeight ω T r (t/T) = ω (t/T)*Real.log (|t|+2)^r := by sorry

theorem tripleBudget_arch_middle (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (y : ℝ) (f g : ℝ → ℂ) :
    tripleSmoothedIntegral ω T f (tripleArch y) g = (1/(y:ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 1 (t/T)/T:ℝ):ℂ)*(f t*star (g t)) := by sorry

theorem tripleBudget_arch_first (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (x : ℝ) (f g : ℝ → ℂ) :
    tripleSmoothedIntegral ω T (tripleArch x) f g = (1/(x:ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 1 (t/T)/T:ℝ):ℂ)*(f t*star (g t)) := by sorry

theorem tripleBudget_PAPoff_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleBudgetError ω T X Y .PAPoff = (1/(Y:ℂ))*
      ∑' p, tripleLogFourierOffTerm (tripleBudgetLogWeight ω T 1) T
        (tripleLogCoefficient X) (tripleLogCoefficient (X*Y)) p := by sorry

theorem tripleBudget_APPoff_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleBudgetError ω T X Y .APPoff = (1/(X:ℂ))*
      ∑' p, tripleLogFourierOffTerm (tripleBudgetLogWeight ω T 1) T
        (tripleLogCoefficient Y) (tripleLogCoefficient (X*Y)) p := by sorry

theorem tripleBudgetWeight_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    Integrable ω := by sorry

theorem tripleBudgetMoment_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (r : ℕ) : Integrable (fun u : ℝ => ω u*Real.log (|T*u|+2)^r) := by sorry

theorem tripleBudgetMoment_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) (r : ℕ) :
    Real.log T^r ≤ tripleBudgetMoment ω T r ∧
      tripleBudgetMoment ω T r ≤ Real.log (2*T+2)^r := by sorry

theorem tripleBudget_archcube_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) :
    0 ≤ (tripleBudgetError ω T X Y .archcube).re ∧
    ‖tripleBudgetError ω T X Y .archcube‖ ≤
      (Real.log (2*T+2)^3-Real.log T^3)/(X*Y)^2 := by sorry

theorem tripleBudgetMixedConstant_nonneg : 0≤ tripleBudgetMixedConstant := by sorry

theorem tripleBudgetCubicConstant_nonneg : 0≤ tripleBudgetCubicConstant := by sorry

theorem tripleBudgetNamedConstant_pos : 0< tripleBudgetNamedConstant := by sorry

theorem tripleBudget_named_interior (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T R X Y : ℝ) (hT : 3≤ T) (hR : 1≤ R) (hXR : R≤ X) (hYR : R≤ Y) (hZ : X*Y≤ T/R) :
    ‖∑ e : TripleBudgetError, tripleBudgetError ω T X Y e‖ ≤
      tripleBudgetNamedConstant*(1+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by sorry

theorem tripleBudget_PPPoff_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleBudgetError ω T X Y .PPPoff =
      -(∑' p, tripleLogFourierOffTerm ω T (tripleLogConvolution X Y)
        (tripleLogCoefficient (X*Y)) p) := by sorry

theorem tripleBudget_PAPoff_gap (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PAPoff‖ ≤
      (tripleBudgetOmega ω T 1/(T*Y))*tripleLogGapBound (tripleLogCoefficient X) (tripleLogCoefficient (X*Y)) := by sorry

theorem tripleBudget_APPoff_gap (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .APPoff‖ ≤
      (tripleBudgetOmega ω T 1/(T*X))*tripleLogGapBound (tripleLogCoefficient Y) (tripleLogCoefficient (X*Y)) := by sorry

theorem tripleBudget_PPPoff_gap (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PPPoff‖ ≤
      (fourierDerivativeL1 ω 1/T)*tripleLogGapBound (tripleLogConvolution X Y) (tripleLogCoefficient (X*Y)) := by sorry

theorem tripleBudget_PAPoff_rate (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PAPoff‖ ≤
      (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
        (tripleBudgetOmega ω T 1/T)*(X/Real.sqrt Y)*
          Real.sqrt (Real.log (2*X)^3*Real.log (2*(X*Y))^3) := by sorry

theorem tripleBudget_APPoff_rate (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .APPoff‖ ≤
      (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
        (tripleBudgetOmega ω T 1/T)*(Y/Real.sqrt X)*
          Real.sqrt (Real.log (2*Y)^3*Real.log (2*(X*Y))^3) := by sorry

theorem tripleBudget_PPPoff_rate (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) :
    ‖tripleBudgetError ω T X Y .PPPoff‖ ≤
      (triplePrimeMassConstant^3/Real.log 2^2+4*Real.sqrt 2*Real.sqrt (tripleDyadicConstant 5*tripleDyadicConstant 3))*
        fourierDerivativeL1 ω 1*(X*Y)*Real.log (2*(X*Y))^4/T := by sorry

theorem tripleBudgetLogWeight_eq_abs (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤ T) (r : ℕ) (u : ℝ) :
    tripleBudgetLogWeight ω T r u = ω u*Real.log (|T*u|+2)^r := by sorry

theorem tripleBudgetLogWeight_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) (r : ℕ) : Integrable (tripleBudgetLogWeight ω T r) := by sorry

theorem tripleBudgetLogWeight_integral (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤ T) (r : ℕ) :
    (∫ u, tripleBudgetLogWeight ω T r u) = tripleBudgetMoment ω T r := by sorry

theorem tripleBudgetLogWeight_zero (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤ T) (r : ℕ) :
    pairMeanFourier (fun u => (tripleBudgetLogWeight ω T r u:ℂ)) 0 = (tripleBudgetMoment ω T r:ℂ) := by sorry

theorem tripleBudgetLogWeight_decay (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤ T) (r : ℕ) (v : ℝ) (hv : v≠0) :
    ‖pairMeanFourier (fun u => (tripleBudgetLogWeight ω T r u:ℂ)) (T/(2*Real.pi)*v)‖ ≤
      tripleBudgetOmega ω T r/(T*|v|) := by sorry

theorem tripleBudgetPrime_sup_mass (x t : ℝ) (hx : 1≤ x) :
    ‖pairPrimeSeries (x,t)‖ ≤ triplePrimeMass x := by sorry

theorem tripleBudgetPrimeL2_mass (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤ T) (hx : 1≤ x) : tripleBudgetPrimeL2 ω T x ≤ triplePrimeMass x := by sorry

theorem tripleBudgetPrime_weighted_square (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (W T x : ℝ) (hW : 0≤ W) (hωW : ∀ u, ω u≤ W) (hT : 3≤ T) (hx : 1≤ x) :
    (∫ t : ℝ, ω (t/T)/T*‖pairPrimeSeries (x,t)‖^2) ≤ (W/T)*pairPrimeMeanSquare x (2*T) := by sorry

theorem tripleBudgetPrimeL2_uniform : ∃ C : ℝ, 0< C ∧ ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ W T x : ℝ, 0≤ W → (∀ u, ω u≤ W) → 3≤ T → 1≤ x → x≤ 2*T →
      tripleBudgetPrimeL2 ω T x ≤ Real.sqrt (2*C*W*Real.log (2*x)) := by sorry

theorem tripleBudget_refinement_algebra {R : Type*} [CommSemiring R] (w : MasterWord)
    (F : Fin 3 → PairRemainderKind → R) (G : Fin 3 → R) :
    (∏ r : Fin 3, if w r = .H then ∑ j, F r j else G r) =
      ∑ κ : TripleBudgetAssignment w, ∏ r : Fin 3,
        if h : w r = .H then F r (κ ⟨r,h⟩) else G r := by sorry

theorem tripleBudgetRefinedComponent_continuous (w : MasterWord)
    (κ : TripleBudgetAssignment w) (r : Fin 3) (x : ℝ) (hx : 1≤ x) :
    Continuous (tripleBudgetRefinedComponent w κ r x) := by sorry

theorem tripleBudgetRefined_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0< T) (hX : 1≤ X) (hY : 1≤ Y) (w : MasterWord)
    (κ : TripleBudgetAssignment w) : Integrable (tripleSmoothedIntegrand ω T
      (tripleBudgetRefinedComponent w κ 0 X) (tripleBudgetRefinedComponent w κ 1 Y)
      (tripleBudgetRefinedComponent w κ 2 (X*Y))) := by sorry

theorem tripleBudget_refinement_pointwise (ω : ℝ → ℝ) (T X Y t : ℝ) (w : MasterWord) :
    tripleWordIntegrand ω T X Y w t =
      ∑ κ : TripleBudgetAssignment w, tripleSmoothedIntegrand ω T
        (tripleBudgetRefinedComponent w κ 0 X) (tripleBudgetRefinedComponent w κ 1 Y)
        (tripleBudgetRefinedComponent w κ 2 (X*Y)) t := by sorry

theorem tripleBudget_refinement (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) (w : MasterWord) :
    tripleBudgetWordError ω T X Y w =
      ∑ κ : TripleBudgetAssignment w, tripleBudgetRefinedError ω T X Y w κ := by sorry

theorem tripleBudgetRemainderBound_nonneg (j : PairRemainderKind) (T x : ℝ)
    (hT : 3≤ T) (hx : 1≤ x) : 0 ≤ tripleBudgetRemainderBound j T x := by sorry

theorem tripleBudget_remainder_bound (j : PairRemainderKind) (T x t : ℝ)
    (hT : 3≤ T) (hx : 1≤ x) (ht : t ∈ Icc T (2*T)) :
    ‖pairRHSRemainder j x t‖ ≤ tripleBudgetRemainderBound j T x := by sorry

theorem tripleBudget_remainder_total_bound (T x t : ℝ)
    (hT : 3≤ T) (hx : 1≤ x) (ht : t ∈ Icc T (2*T)) :
    ‖tripleComponent .H x t‖ ≤ tripleBudgetRemainderTotal T x := by sorry

theorem tripleBudget_arch_bound (T x t : ℝ)
    (hT : 3≤ T) (hx : 1≤ x) (ht : t ∈ Icc T (2*T)) :
    ‖tripleComponent .A x t‖ ≤ tripleBudgetAlpha T x := by sorry

theorem tripleBudget_integral_first_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h)
    (B : ℝ) (hB : 0≤ B) (hb : ∀ t ∈ Icc T (2*T), ‖f t‖≤ B) :
    ‖tripleSmoothedIntegral ω T f g h‖ ≤ tripleBudgetL2 ω T g*tripleBudgetL2 ω T h*B := by sorry

theorem tripleBudget_integral_second_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f g h : ℝ → ℂ) (hf : Continuous f) (hh : Continuous h)
    (B : ℝ) (hB : 0≤ B) (hb : ∀ t ∈ Icc T (2*T), ‖g t‖≤ B) :
    ‖tripleSmoothedIntegral ω T f g h‖ ≤ tripleBudgetL2 ω T f*tripleBudgetL2 ω T h*B := by sorry

theorem tripleBudget_slots_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0< T) (f : Fin 3 → ℝ → ℂ) (hf : ∀ r, Continuous (f r))
    (B : Fin 3 → ℝ) (hB : ∀ r, 0≤ B r) (hL : ∀ r, tripleBudgetL2 ω T (f r)≤ B r)
    (r : Fin 3) (hs : ∀ t ∈ Icc T (2*T), ‖f r t‖≤ B r) :
    ‖tripleSmoothedIntegral ω T (f 0) (f 1) (f 2)‖ ≤ ∏ r : Fin 3, B r := by sorry

theorem triplePrimeMassConstant_closed :
    triplePrimeMassConstant = 1+2/(1-1/Real.sqrt 2)^2 := by sorry

theorem tripleBudgetPrimeB_nonneg (x : ℝ) (hx : 1≤ x) : 0≤ tripleBudgetPrimeB x := by sorry

theorem tripleBudgetPrimeM_nonneg (C W T x : ℝ) (hx : 1≤ x) : 0≤ tripleBudgetPrimeM C W T x := by sorry

theorem tripleBudgetPrimeM_endpoint (C W T : ℝ) :
    tripleBudgetPrimeM C W T (2*T) =
      min (tripleBudgetPrimeB (2*T)) (Real.sqrt (2*C*W*Real.log (4*T))) := by sorry

theorem tripleBudgetPrime_norm_envelope : ∃ C : ℝ, 0< C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T x : ℝ,
      0≤ W → (∀ u, ω u≤ W) → 3≤ T → 1≤ x →
        tripleBudgetPrimeL2 ω T x ≤ tripleBudgetPrimeM C W T x := by sorry

theorem tripleBudgetPrime_sup_envelope (x t : ℝ) (hx : 1≤ x) :
    ‖pairPrimeSeries (x,t)‖≤ tripleBudgetPrimeB x := by sorry

theorem tripleBudgetLetterNorm_nonneg (ω : ℝ → ℝ) (T x : ℝ) (hT : 3≤ T) (hx : 1≤ x) (l : MasterLetter) :
    0≤ tripleBudgetLetterNorm ω T x l := by sorry

theorem tripleBudget_component_L2 (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤ T) (hx : 1≤ x) (l : MasterLetter) :
    tripleBudgetL2 ω T (tripleComponent l x) ≤ tripleBudgetLetterNorm ω T x l := by sorry

theorem tripleBudgetRefinedNorm_nonneg (ω : ℝ → ℝ) (T x : ℝ) (hT : 3≤ T) (hx : 1≤ x)
    (w : MasterWord) (κ : TripleBudgetAssignment w) (r : Fin 3) :
    0≤ tripleBudgetRefinedNorm ω T x w κ r := by sorry

theorem tripleBudget_refined_L2 (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤ T) (hx : 1≤ x) (w : MasterWord) (κ : TripleBudgetAssignment w) (r : Fin 3) :
    tripleBudgetL2 ω T (tripleBudgetRefinedComponent w κ r x) ≤ tripleBudgetRefinedNorm ω T x w κ r := by sorry

theorem tripleWordSign_norm (w : MasterWord) : ‖(tripleWordSign w:ℂ)‖=1 := by sorry

theorem tripleBudget_refined_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) (w : MasterWord)
    (hw : tripleWordHasH w = true) (κ : TripleBudgetAssignment w) :
    ‖tripleBudgetRefinedError ω T X Y w κ‖ ≤
      ∏ r : Fin 3, tripleBudgetRefinedNorm ω T (![X,Y,X*Y] r) w κ r := by sorry

theorem tripleBudget_word_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) (w : MasterWord)
    (hw : tripleWordHasH w = true) :
    ‖tripleBudgetWordError ω T X Y w‖ ≤ ∏ r : Fin 3, tripleBudgetLetterNorm ω T (![X,Y,X*Y] r) (w r) := by sorry

theorem tripleMultiplicativeWeight_product (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) (m n : ℕ) :
    tripleMultiplicativeWeight X m*tripleMultiplicativeWeight Y n ≤
      tripleMultiplicativeWeight (X*Y) (m*n) := by sorry

theorem tripleArithmeticCoefficient_product (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) (m n : ℕ) :
    tripleArithmeticCoefficient X m*tripleArithmeticCoefficient Y n ≤
      (ArithmeticFunction.vonMangoldt m*ArithmeticFunction.vonMangoldt n)/Real.sqrt (m*n) *
        tripleMultiplicativeWeight (X*Y) (m*n) := by sorry

theorem tripleArithmeticConvolution_nonneg (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) (r : ℕ) :
    0≤ tripleArithmeticConvolution X Y r := by sorry

theorem tripleArithmeticConvolution_bound (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) (r : ℕ) (hr : 1≤ r) :
    tripleArithmeticConvolution X Y r ≤
      tripleMultiplicativeWeight (X*Y) r*Real.log r^2/Real.sqrt r := by sorry

theorem tripleLogConvolution_energy_pointwise (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) (n : LogGapIndex) :
    tripleLogEnergyTerm (tripleLogConvolution X Y) n ≤ tripleDyadicMoment (X*Y) 5 n.val := by sorry

theorem tripleLogConvolution_energy_summable (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    Summable (tripleLogEnergyTerm (tripleLogConvolution X Y)) := by sorry

theorem tripleLogConvolution_energy_bound (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleLogEnergy (tripleLogConvolution X Y) ≤ tripleDyadicConstant 5*(X*Y)*Real.log (2*(X*Y))^5 := by sorry

theorem tripleArithmeticCoefficient_le_mass (x : ℝ) (hx : 1≤ x) (n : ℕ) :
    tripleArithmeticCoefficient x n ≤ triplePrimeMass x := by sorry

theorem tripleArithmetic_resonance_summable (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    Summable (fun p : ℕ × ℕ => tripleArithmeticCoefficient X p.1*tripleArithmeticCoefficient Y p.2*
      tripleArithmeticCoefficient (X*Y) (p.1*p.2)) := by sorry

theorem tripleArithmetic_resonance_sum (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    (∑' p : ℕ × ℕ, tripleArithmeticCoefficient X p.1*tripleArithmeticCoefficient Y p.2*
      tripleArithmeticCoefficient (X*Y) (p.1*p.2)) = triplePrimeResonantMass X Y := by sorry

theorem tripleArithmeticConvolution_diagonal (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    (∑' r, tripleArithmeticConvolution X Y r*tripleArithmeticCoefficient (X*Y) r) =
      triplePrimeResonantMass X Y := by sorry

theorem tripleLogConvolution_diagonal (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    (∑' n, tripleLogConvolution X Y n*star (tripleLogCoefficient (X*Y) n)) =
      (triplePrimeResonantMass X Y:ℂ) := by sorry

theorem tripleArithmeticConvolution_fiber (X Y : ℝ) (r : ℕ) :
    tripleArithmeticConvolution X Y r =
      ∑' p : (fun q : ℕ × ℕ => q.1*q.2) ⁻¹' {r},
        tripleArithmeticCoefficient X p.val.1*tripleArithmeticCoefficient Y p.val.2 := by sorry

theorem tripleArithmeticCoefficient_mass (x : ℝ) (hx : 1≤ x) :
    (∑' n, tripleArithmeticCoefficient x n) = triplePrimeMass x := by sorry

theorem tripleArithmeticConvolution_hasSum (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    HasSum (tripleArithmeticConvolution X Y) (triplePrimeMass X*triplePrimeMass Y) := by sorry

theorem tripleArithmeticConvolution_summable (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    Summable (tripleArithmeticConvolution X Y) := by sorry

theorem tripleArithmeticConvolution_mass (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    (∑' r, tripleArithmeticConvolution X Y r) = triplePrimeMass X*triplePrimeMass Y := by sorry

theorem tripleLogConvolution_mass_summable (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    Summable (fun n => ‖tripleLogConvolution X Y n‖) := by sorry

theorem tripleLogConvolution_mass_bound (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleLogMass (tripleLogConvolution X Y) ≤ triplePrimeMass X*triplePrimeMass Y := by sorry

theorem tripleNatBall_nonneg (R c : ℝ) (hc : 0≤ c) (n : ℕ) : 0≤ tripleNatBall R c n := by sorry

theorem tripleNatBall_support (R c : ℝ) (n : ℕ) (hn : n∉Finset.Icc 1 ⌊R⌋₊) : tripleNatBall R c n = 0 := by sorry

theorem tripleNatBall_summable (R c : ℝ) : Summable (tripleNatBall R c) := by sorry

theorem tripleNatBall_sum (R c : ℝ) (hR : 0≤ R) :
    (∑' n, tripleNatBall R c n) = (⌊R⌋₊:ℝ)*c := by sorry

theorem tripleNatBall_bound (R c : ℝ) (hR : 0≤ R) (hc : 0≤ c) :
    (∑' n, tripleNatBall R c n) ≤ R*c := by sorry

theorem tripleDyadic_geometric_summable (k : ℕ) :
    Summable (fun j : ℕ => (1/2:ℝ)^j*(j+2:ℝ)^k) := by sorry

theorem tripleDyadicConstant_pos (k : ℕ) : 0< tripleDyadicConstant k := by sorry

theorem tripleDyadicBall_nonneg (x : ℝ) (hx : 1≤ x) (k j n : ℕ) :
    0≤ tripleDyadicBall x k j n := by sorry

theorem tripleDyadicBall_bound (x : ℝ) (hx : 1≤ x) (k j : ℕ) :
    (∑' n, tripleDyadicBall x k j n) ≤
      (2*x*Real.log (2*x)^k)*((1/2:ℝ)^j*(j+2:ℝ)^k) := by sorry

theorem tripleDyadicBall_double_summable (x : ℝ) (hx : 1≤ x) (k : ℕ) :
    Summable (fun p : ℕ × ℕ => tripleDyadicBall x k p.1 p.2) := by sorry

theorem tripleMultiplicativeWeight_nonneg (x : ℝ) (hx : 0≤ x) (n : ℕ) :
    0≤ tripleMultiplicativeWeight x n := by sorry

theorem tripleDyadicMoment_nonneg (x : ℝ) (k n : ℕ) : 0≤ tripleDyadicMoment x k n := by sorry

theorem tripleDyadicMoment_head (x : ℝ) (hx : 1≤ x) (k n : ℕ) (hn : (n:ℝ)≤ x) :
    tripleDyadicMoment x k n ≤ tripleNatBall x (Real.log (2*x)^k) n := by sorry

theorem tripleDyadicMoment_tail_cover (x : ℝ) (hx : 1≤ x) (k n : ℕ) (hn : x<(n:ℝ)) :
    ∃ j : ℕ, tripleDyadicMoment x k n ≤ tripleDyadicBall x k j n := by sorry

theorem tripleDyadicMoment_majorant (x : ℝ) (hx : 1≤ x) (k n : ℕ) :
    tripleDyadicMoment x k n ≤ tripleNatBall x (Real.log (2*x)^k) n +
      ∑' j, tripleDyadicBall x k j n := by sorry

theorem tripleDyadicMoment_summable (x : ℝ) (hx : 1≤ x) (k : ℕ) :
    Summable (tripleDyadicMoment x k) := by sorry

theorem tripleDyadicMoment_bound (x : ℝ) (hx : 1≤ x) (k : ℕ) :
    (∑' n, tripleDyadicMoment x k n) ≤ tripleDyadicConstant k*x*Real.log (2*x)^k := by sorry

theorem tripleFiniteSchur {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (K : ι → κ → ℝ) (u : ι → ℝ) (v : κ → ℝ) (A : ι → ℝ) (B : κ → ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ t, 0≤ K i j)
    (hA : ∀ i ∈ s, ∑ j ∈ t, K i j ≤ A i)
    (hB : ∀ j ∈ t, ∑ i ∈ s, K i j ≤ B j) :
    (∑ i ∈ s, ∑ j ∈ t, K i j*u i*v j) ≤
      Real.sqrt ((∑ i ∈ s, A i*u i^2)*(∑ j ∈ t, B j*v j^2)) := by sorry

theorem tripleLogGap_mixed_rate (x y : ℝ) (hx : 1≤ x) (hy : 1≤ y) :
    tripleLogGapBound (tripleLogCoefficient x) (tripleLogCoefficient y) ≤
      (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
        (Real.sqrt x*Real.sqrt y)*Real.sqrt (Real.log (2*x)^3*Real.log (2*y)^3) := by sorry

theorem tripleLogGap_cubic_rate (X Y : ℝ) (hX : 1≤ X) (hY : 1≤ Y) :
    tripleLogGapBound (tripleLogConvolution X Y) (tripleLogCoefficient (X*Y)) ≤
      (triplePrimeMassConstant^3/Real.log 2^2+4*Real.sqrt 2*Real.sqrt (tripleDyadicConstant 5*tripleDyadicConstant 3))*
        (X*Y)*Real.log (2*(X*Y))^4 := by sorry

theorem pairMeanWeighted_linear_identity {ι : Type*} [Countable ι]
    (μ : ι → ℝ) (c : ι → ℂ) (hc : Summable (fun n => ‖c n‖))
    (M : ℝ → ℂ) (hM : Integrable M) :
    (∫ t, M t*pairFrequencySum μ c t) = ∑' n, c n*pairMeanFourier M (-μ n) := by sorry

theorem tripleLog_linear_identity (φ : ℝ → ℝ) (hφ : Integrable φ)
    (T : ℝ) (hT : 0< T) (c : LogGapIndex → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    (∫ t, ((φ (t/T)/T:ℝ):ℂ)*pairFrequencySum tripleLogFrequency c t) =
      ∑' n, c n*pairMeanFourier (fun u => (φ u:ℂ)) (T/(2*Real.pi)*Real.log n.val) := by sorry

theorem tripleLog_linear_decay (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0< T) (n : LogGapIndex) :
    ‖pairMeanFourier (fun u => (φ u:ℂ)) (T/(2*Real.pi)*Real.log n.val)‖ ≤
      fourierDerivativeL1 φ 1/(T*Real.log n.val) := by sorry

theorem tripleLogCoefficient_div_log_summable (x : ℝ) (hx : 1≤ x) :
    Summable (fun n : LogGapIndex => tripleArithmeticCoefficient x n.val/Real.log n.val) := by sorry

theorem tripleLogCoefficient_div_log_bound (x : ℝ) (hx : 1≤ x) :
    (∑' n : LogGapIndex, tripleArithmeticCoefficient x n.val/Real.log n.val) ≤ 5*Real.sqrt x := by sorry

theorem tripleBudget_single_prime_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤ T) (hx : 1≤ x) (r : ℕ) :
    ‖∫ t, ((tripleBudgetLogWeight ω T r (t/T)/T:ℝ):ℂ)*pairPrimeSeries (x,t)‖ ≤
      5*Real.sqrt x*tripleBudgetOmega ω T r/T := by sorry

theorem tripleLogFourier_summable (φ : ℝ → ℝ) (T : ℝ) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    Summable (fun p => ‖tripleLogFourierTerm φ T c d p‖) := by sorry

theorem tripleLogFourier_identity (φ : ℝ → ℝ) (hφ : Integrable φ)
    (T : ℝ) (hT : 0< T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    (∫ t, ((φ (t/T)/T:ℝ):ℂ)*(pairFrequencySum tripleLogFrequency c t *
      star (pairFrequencySum tripleLogFrequency d t))) =
      ∑' p, tripleLogFourierTerm φ T c d p := by sorry

theorem tripleLogFourier_diagonal (φ : ℝ → ℝ) (T : ℝ) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    (∑' p, tripleLogFourierTerm φ T c d p) =
      (∑' n, c n*star (d n))*pairMeanFourier (fun u => (φ u:ℂ)) 0 +
        ∑' p, tripleLogFourierOffTerm φ T c d p := by sorry

theorem tripleLogFourier_off_identity (φ : ℝ → ℝ) (hφ : Integrable φ)
    (T : ℝ) (hT : 0< T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    (∫ t, ((φ (t/T)/T:ℝ):ℂ)*(pairFrequencySum tripleLogFrequency c t *
      star (pairFrequencySum tripleLogFrequency d t))) -
        (∑' n, c n*star (d n))*(∫ u, (φ u:ℂ)) =
      ∑' p, tripleLogFourierOffTerm φ T c d p := by sorry

theorem tripleLogEnergyTerm_nonneg (c : LogGapIndex → ℂ) (n : LogGapIndex) :
    0≤ tripleLogEnergyTerm c n := by sorry

theorem tripleLogGapTerm_nonneg (c d : LogGapIndex → ℂ) (p : LogGapIndex × LogGapIndex) :
    0≤ tripleLogGapTerm c d p := by sorry

theorem tripleLogGap_rectangle (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d))
    (s t : Finset LogGapIndex) :
    (∑ m ∈ s, ∑ n ∈ t, tripleLogGapTerm c d (m,n)) ≤ tripleLogGapBound c d := by sorry

theorem tripleLogGap_finite_subset (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d))
    (s : Finset (LogGapIndex × LogGapIndex)) :
    (∑ p ∈ s, tripleLogGapTerm c d p) ≤ tripleLogGapBound c d := by sorry

theorem tripleLogGap_summable (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    Summable (tripleLogGapTerm c d) := by sorry

theorem tripleLogGap_bound (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    (∑' p, tripleLogGapTerm c d p) ≤ tripleLogGapBound c d := by sorry

theorem tripleComparableKernel_nonneg (m n : ℕ) : 0≤ tripleComparableKernel m n := by sorry

theorem tripleComparableKernel_swap (m n : ℕ) :
    tripleComparableKernel m n = tripleComparableKernel n m := by sorry

theorem tripleComparableKernel_row (s : Finset ℕ) (m : ℕ) (hm : 2≤ m) :
    (∑ n ∈ s, tripleComparableKernel m n) ≤ 4*Real.log (2*m) := by sorry

theorem tripleLogGap_term (m n : ℕ) (hm : 2≤ m) (hn : 2≤ n) (a b : ℝ)
    (ha : 0≤ a) (hb : 0≤ b) :
    (if m=n then 0 else a*b/|Real.log ((m:ℝ)/n)|) ≤
      a*b/Real.log 2 + Real.sqrt 2 *
        (tripleComparableKernel m n*(Real.sqrt m*a)*(Real.sqrt n*b)) := by sorry

theorem tripleLogGap_finite (s t : Finset ℕ) (hs : ∀ m ∈ s, 2≤ m) (ht : ∀ n ∈ t, 2≤ n)
    (a b : ℕ → ℝ) (ha : ∀ m, 0≤ a m) (hb : ∀ n, 0≤ b n) :
    (∑ m ∈ s, ∑ n ∈ t, if m=n then 0 else a m*b n/|Real.log ((m:ℝ)/n)|) ≤
      (∑ m ∈ s, a m)*(∑ n ∈ t, b n)/Real.log 2 + 4*Real.sqrt 2 *
        Real.sqrt ((∑ m ∈ s, (m:ℝ)*Real.log (2*m)*a m^2)*
          (∑ n ∈ t, (n:ℝ)*Real.log (2*n)*b n^2)) := by sorry

theorem tripleLogGap_nonzero (m n : ℝ) (hm : 0< m) (hn : 0< n) (hne : m≠n) :
    0 < |Real.log (m/n)| := by sorry

theorem tripleLogGap_inverse (m n : ℝ) (hm : 0< m) (hn : 0< n) (hne : m≠n) :
    1/|Real.log (m/n)| ≤ max m n/|m-n| := by sorry

theorem tripleLogGap_far (m n : ℝ) (hm : 0< m) (hn : 0< n)
    (hfar : n< m/2 ∨ 2*m< n) : 1/|Real.log (m/n)| ≤ 1/Real.log 2 := by sorry

theorem tripleLogGap_comparable_max (m n : ℝ) (hm : 0< m) (hn : 0< n)
    (hlo : m/2≤ n) (hhi : n≤ 2*m) : max m n ≤ Real.sqrt 2 * Real.sqrt m * Real.sqrt n := by sorry

theorem tripleLogGap_comparable (m n : ℝ) (hm : 0< m) (hn : 0< n) (hne : m≠n)
    (hlo : m/2≤ n) (hhi : n≤ 2*m) :
    1/|Real.log (m/n)| ≤ Real.sqrt 2 * Real.sqrt m * Real.sqrt n/|m-n| := by sorry

theorem tripleLogGap_row (s : Finset ℕ) (m : ℕ) (hm : 2≤ m)
    (hs : ∀ n ∈ s, n≤ 2*m ∧ n≠m) :
    (∑ n ∈ s, 1/|(m:ℝ)-n|) ≤ 4*Real.log (2*m) := by sorry

theorem pairFrequencySum_cross_expansion {ι κ : Type*}
    (μ : ι → ℝ) (ν : κ → ℝ) (c : ι → ℂ) (d : κ → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (hd : Summable (fun j => ‖d j‖)) (t : ℝ) :
    pairFrequencySum μ c t * star (pairFrequencySum ν d t) =
      ∑' p : ι × κ, c p.1*star (d p.2)*pairMeanCharacter ((μ p.1-ν p.2)*t) := by sorry

theorem pairMeanWeighted_cross_identity {ι κ : Type*} [Countable ι] [Countable κ]
    (μ : ι → ℝ) (ν : κ → ℝ) (c : ι → ℂ) (d : κ → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (hd : Summable (fun j => ‖d j‖))
    (M : ℝ → ℂ) (hM : Integrable M) :
    (∫ t, M t*(pairFrequencySum μ c t*star (pairFrequencySum ν d t))) =
      ∑' p : ι × κ, c p.1*star (d p.2)*pairMeanFourier M (ν p.2-μ p.1) := by sorry

theorem pairMeanFourier_normalized (φ : ℝ → ℝ) (T ξ : ℝ) (hT : 0< T) :
    pairMeanFourier (fun t => ((φ (t/T)/T:ℝ):ℂ)) ξ =
      pairMeanFourier (fun u => (φ u:ℂ)) (T*ξ) := by sorry

theorem tripleLogFrequency_difference (m n : LogGapIndex) :
    tripleLogFrequency n-tripleLogFrequency m = Real.log ((m.val:ℝ)/n.val)/(2*Real.pi) := by sorry

theorem tripleLogFrequency_gap_ne (m n : LogGapIndex) (h : m≠n) :
    Real.log ((m.val:ℝ)/n.val)≠0 := by sorry

theorem tripleLogFourierOffTerm_bound (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0< T) (c d : LogGapIndex → ℂ)
    (p : LogGapIndex × LogGapIndex) :
    ‖tripleLogFourierOffTerm φ T c d p‖ ≤
      (fourierDerivativeL1 φ 1/T)*tripleLogGapTerm c d p := by sorry

theorem tripleLogFourierOff_summable (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0< T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    Summable (fun p => ‖tripleLogFourierOffTerm φ T c d p‖) := by sorry

theorem tripleLogFourierOff_bound (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0< T) (c d : LogGapIndex → ℂ)
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖))
    (hec : Summable (tripleLogEnergyTerm c)) (hed : Summable (tripleLogEnergyTerm d)) :
    ‖∑' p, tripleLogFourierOffTerm φ T c d p‖ ≤
      (fourierDerivativeL1 φ 1/T)*tripleLogGapBound c d := by sorry

theorem triplePrimeMassRatio_range : 0< triplePrimeMassRatio ∧ triplePrimeMassRatio<1 := by sorry

theorem triplePrimeMass_geometric_summable :
    Summable (fun j : ℕ => triplePrimeMassRatio^j*(j+1:ℝ)) := by sorry

theorem triplePrimeMassConstant_pos : 0< triplePrimeMassConstant := by sorry

theorem triplePrimeMassBall_nonneg (x : ℝ) (hx : 1≤ x) (j n : ℕ) :
    0≤ triplePrimeMassBall x j n := by sorry

theorem triplePrimeMassBall_bound (x : ℝ) (hx : 1≤ x) (j : ℕ) :
    (∑' n, triplePrimeMassBall x j n) ≤
      (2*Real.sqrt x*Real.log (2*x))*(triplePrimeMassRatio^j*(j+1:ℝ)) := by sorry

theorem triplePrimeMassBall_double_summable (x : ℝ) (hx : 1≤ x) :
    Summable (fun p : ℕ × ℕ => triplePrimeMassBall x p.1 p.2) := by sorry

theorem tripleArithmeticCoefficient_head (x R : ℝ) (hx : 0< x) (n : ℕ) (hn : (n:ℝ)≤ R) :
    tripleArithmeticCoefficient x n ≤ ArithmeticFunction.vonMangoldt n*Real.sqrt R/x := by sorry

theorem tripleArithmeticCoefficient_tail (x R : ℝ) (hx : 0< x) (hR : 0< R) (n : ℕ) (hn : R≤(n:ℝ)) :
    tripleArithmeticCoefficient x n ≤ ArithmeticFunction.vonMangoldt n*x/(R*Real.sqrt R) := by sorry

theorem triplePrimeMass_head (x : ℝ) (hx : 1≤ x) (n : ℕ) (hn : (n:ℝ)≤ x) :
    tripleArithmeticCoefficient x n ≤ tripleNatBall x (Real.log (2*x)/Real.sqrt x) n := by sorry

theorem triplePrimeMass_tail_cover (x : ℝ) (hx : 1≤ x) (n : ℕ) (hn : x<(n:ℝ)) :
    ∃ j : ℕ, tripleArithmeticCoefficient x n ≤ triplePrimeMassBall x j n := by sorry

theorem triplePrimeMass_bound (x : ℝ) (hx : 1≤ x) :
    triplePrimeMass x ≤ triplePrimeMassConstant*Real.sqrt x*Real.log (2*x) := by sorry

theorem tripleArithmeticConvolution_below_four (X Y : ℝ) (r : ℕ) (hr : r<4) :
    tripleArithmeticConvolution X Y r=0 := by sorry

theorem tripleBudget_same_sign_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤ T) (hX : 1≤ X) (hY : 1≤ Y) (r : ℕ) :
    ‖∫ t, ((tripleBudgetLogWeight ω T r (t/T)/T:ℝ):ℂ)*
      (pairPrimeSeries (X,t)*pairPrimeSeries (Y,t))‖ ≤
      triplePrimeMass X*triplePrimeMass Y*tripleBudgetOmega ω T r/(T*Real.log 4) := by sorry

end
end HigherCorrelations
