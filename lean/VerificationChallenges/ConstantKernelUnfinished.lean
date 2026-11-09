import HigherCorrelations.ConstantReplacementDefinitions
import HigherCorrelations.UniformHeightDefinitions
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

theorem constantKernelEmpty_profile (a d : ℝ) (δ : Fin 3 → ℝ) :
    constantKernelEmpty a d δ = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      rationalProfile a d (if e 1 then -δ 1 else δ 1)
        (if e 2 then -δ 2 else δ 2) (if e 0 then -δ 0 else δ 0) := by sorry

theorem constantKernelEmpty_symmetric (a d : ℝ) (δ : Fin 3 → ℝ) :
    constantKernelEmpty a d δ = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      (horizontalProfile a d (constantKernelParameters δ e)+
        horizontalProfile a d (-constantKernelParameters δ e))/2 := by sorry

theorem constantKernelEmpty_horizontal_bound (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a d δ-rationalProfile a d 0 0 0‖ ≤
      3072*Real.pi*(∑ j, δ j^2) := by sorry

theorem constantKernelEmpty_global_bound (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) : ‖constantKernelEmpty a d δ‖ ≤ 7*Real.pi/9 := by sorry

theorem constantKernel_real_gap_bound (a d : ℝ) (hg : a^2+d^2 ≤ 1) :
    ‖rationalProfile a d 0 0 0-kernelBenchmark‖ ≤ 4*Real.pi*(a^2+d^2) := by sorry

theorem constantKernelEmpty_pointwise (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a d δ-kernelBenchmark‖ ≤
      constantKernelBound*min (constantKernelEnergy a d δ) 1 := by sorry

theorem constantKernelEmpty_origin : constantKernelEmpty 0 0 0 = kernelBenchmark := by sorry

theorem constantKernelEmpty_coincident (a : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a a δ-kernelBenchmark‖ ≤
      constantKernelBound*min (2*a^2+∑ j, δ j^2) 1 := by sorry

theorem constantKernelEmpty_cube_endpoints (a d : ℝ) (e : Fin 3 → Bool) :
    ‖constantKernelEmpty a d (fun j => if e j then -(1/2) else 1/2)-kernelBenchmark‖ ≤
      constantKernelBound*min (a^2+d^2+3/4) 1 := by sorry

theorem replacementRadius_nonneg (T : ℝ) (v : ReplacementTriple) :
    0 ≤ replacementRadius T v := by sorry

theorem replacementHorizontal_bounds (T : ℝ) (hq : 0 ≤ Real.log T) (v : ReplacementTriple) :
    0 ≤ replacementHorizontal T v ∧ replacementHorizontal T v ≤ Real.log T/2 ∧
    ∀ j, Real.log T*|replacementDelta v j| ≤ replacementHorizontal T v := by sorry

theorem constantKernelEmpty_scaled (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) (q ℓ r x : ℝ)
    (hq : 0 < q) (hℓ : 0 < ℓ) (hr : 0≤r) (hx : 0≤x)
    (hscale : q ≤ 4*Real.pi*ℓ) (ha : |ℓ*a|≤r) (hd : |ℓ*d|≤r)
    (hh : ∀ j, q*|δ j|≤x) :
    ‖constantKernelEmpty a d δ-kernelBenchmark‖ ≤
      replacementScaleConstant*(r^2+x^2)/q^2 := by sorry

theorem replacementKernel_scaled (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (v : ReplacementTriple) :
    ‖replacementKernel v-kernelBenchmark‖ ≤ replacementScaleConstant*
      ((replacementRadius T v)^2+(replacementHorizontal T v)^2)/(Real.log T)^2 := by sorry

theorem replacementPartial_smooth (j : Bool) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (replacementPartial j f) := by sorry

theorem replacementDeriv_succ (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ) :
    replacementDeriv j (n+1) f = replacementPartial j (replacementDeriv j n f) := by sorry

theorem replacementDeriv_succ_right (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ) :
    replacementDeriv j (n+1) f = replacementDeriv j n (replacementPartial j f) := by sorry

theorem replacementDeriv_smooth (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (replacementDeriv j n f) := by sorry

theorem replacementDeriv_support (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ) :
    tsupport (replacementDeriv j n f) ⊆ tsupport f := by sorry

theorem replacementDeriv_compact (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ)
    (hc : HasCompactSupport f) : HasCompactSupport (replacementDeriv j n f) := by sorry

theorem replacementDeriv_integrable (j : Bool) (n : ℕ) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Integrable (replacementDeriv j n f) := by sorry

theorem replacementDeriv_add (j : Bool) (n : ℕ) (f g : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    replacementDeriv j n (fun p => f p+g p) = fun p => replacementDeriv j n f p+replacementDeriv j n g p := by sorry

theorem replacementDeriv_product_bound (j : Bool) (n : ℕ) (f g : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ k ≤ n, ‖replacementDeriv j k f p‖ ≤ A)
    (hgb : ∀ k ≤ n, ‖replacementDeriv j k g p‖ ≤ B) :
    ‖replacementDeriv j n (fun p => f p*g p) p‖  ≤  2^n*A*B := by sorry

theorem replacementP24_nonneg (φ : ℝ × ℝ → ℂ) : 0  ≤  replacementP24 φ := by sorry

theorem replacementP24_pure (φ : ℝ × ℝ → ℂ) (j : Bool) (n : ℕ) (hn : n ≤ 24) :
    (∫ p, ‖replacementDeriv j n φ p‖)  ≤  replacementP24 φ := by sorry

theorem replacementExpRemainder_smooth (L : (ℝ × ℝ) →L[ℝ] ℂ) :
    ContDiff ℝ ∞ (replacementExpRemainder L) := by sorry

theorem replacementPartial_exp (j : Bool) (c : ℂ) (L : (ℝ × ℝ) →L[ℝ] ℂ) :
    replacementPartial j (fun p => c*Complex.exp (L p)) =
      fun p => c*L (replacementCoordinate j)*Complex.exp (L p) := by sorry

theorem replacementExpRemainder_first (j : Bool) (L : (ℝ × ℝ) →L[ℝ] ℂ) :
    replacementDeriv j 1 (replacementExpRemainder L) =
      fun p => L (replacementCoordinate j)*(Complex.exp (L p)-1) := by sorry

theorem replacementExpRemainder_higher (j : Bool) (L : (ℝ × ℝ) →L[ℝ] ℂ) (n : ℕ) :
    replacementDeriv j (n+2) (replacementExpRemainder L) =
      fun p => (L (replacementCoordinate j))^(n+2)*Complex.exp (L p) := by sorry

theorem replacementExpRemainder_jet_bound (j : Bool) (L : (ℝ × ℝ) →L[ℝ] ℂ)
    (p : ℝ × ℝ) (x R : ℝ) (hx : 0 ≤ x) (hL : ‖L p‖ ≤ 2*x)
    (hR : ‖L p‖ ≤ R) (hc : ‖L (replacementCoordinate j)‖ ≤ 2*x)
    (n : ℕ) (hn : n ≤ 22) :
    ‖replacementDeriv j n (replacementExpRemainder L) p‖  ≤
      2^24*x^2*(1+x)^22*Real.exp R := by sorry

theorem replacementFourier_partial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (j : Bool) (u : ℝ × ℝ) :
    complexFourier (replacementPartial j f) ((u.1:ℂ),(u.2:ℂ)) =
      -(2*Real.pi*Complex.I*(if j then u.2 else u.1))*complexFourier f ((u.1:ℂ),(u.2:ℂ)) := by sorry

theorem replacementFourier_power (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (j : Bool) (n : ℕ) (u : ℝ × ℝ) :
    (2*Real.pi*|if j then u.2 else u.1|)^n*‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖ =
      ‖complexFourier (replacementDeriv j n f) ((u.1:ℂ),(u.2:ℂ))‖ := by sorry

theorem replacementFourier_L1 (f : ℝ × ℝ → ℂ) (u : ℝ × ℝ) :
    ‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖  ≤  ∫ p, ‖f p‖ := by sorry

theorem replacementFourier_decay (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (A : ℝ) (hA : 0 ≤ A)
    (h0 : (∫ p, ‖f p‖) ≤ A)
    (h22 : ∀ j, (∫ p, ‖replacementDeriv j 22 f p‖) ≤ A) (u : ℝ × ℝ) :
    ‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖  ≤
      2^22*A/(1+max |u.1| |u.2|)^22 := by sorry

theorem replacementLinear_apply (θ : Fin 3 → ℝ) (e : Fin 3 → Bool) (p : ℝ × ℝ) :
    replacementLinear θ e p = ((replacementSigned θ e 0*(p.1+p.2)+
      replacementSigned θ e 1*p.1+replacementSigned θ e 2*p.2:ℝ):ℂ) := by sorry

theorem replacementLinear_bounds (θ : Fin 3 → ℝ) (e : Fin 3 → Bool) (x s : ℝ)
    (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x) (p : ℝ × ℝ)
    (hp : signedGauge p ≤ s) :
    ‖replacementLinear θ e p‖ ≤ 2*s*x ∧ ‖replacementLinear θ e p‖ ≤ 2*x ∧
    ∀ j, ‖replacementLinear θ e (replacementCoordinate j)‖ ≤ 2*x := by sorry

theorem replacementLinear_sum_zero (θ : Fin 3 → ℝ) (p : ℝ × ℝ) :
    (∑ e : Fin 3 → Bool, replacementLinear θ e p)=0 := by sorry

theorem replacementCosh_remainders (θ : Fin 3 → ℝ) (p : ℝ × ℝ) :
    replacementCosh 1 θ p = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      replacementExpRemainder (replacementLinear θ e) p := by sorry

theorem replacementAmplitude_L1 (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (e : Fin 3 → Bool)
    (x s : ℝ) (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (j : Bool) (n : ℕ) (hn : n ≤ 22) :
    (∫ p, ‖replacementDeriv j n (fun p => φ p*replacementExpRemainder (replacementLinear θ e) p) p‖)  ≤
      2^22*23*replacementP24 φ*(2^24*x^2*(1+x)^22*Real.exp (2*s*x)) := by sorry

theorem replacementRemainder_fourier_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (e : Fin 3 → Bool)
    (x s : ℝ) (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (u : ℝ × ℝ) :
    ‖complexFourier (fun p => φ p*replacementExpRemainder (replacementLinear θ e) p)
      ((u.1:ℂ),(u.2:ℂ))‖  ≤
      replacementDecayConstant*replacementP24 φ*x^2*(1+x)^22*Real.exp (2*s*x)/
        (1+max |u.1| |u.2|)^22 := by sorry

theorem replacementCosh_smooth (θ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (replacementCosh 1 θ) := by sorry

theorem replacementCosh_fourier_sum (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (u : ℝ × ℝ) :
    complexFourier (fun p => φ p*replacementCosh 1 θ p) ((u.1:ℂ),(u.2:ℂ)) =
      (1/8:ℂ)*∑ e : Fin 3 → Bool, complexFourier
        (fun p => φ p*replacementExpRemainder (replacementLinear θ e) p) ((u.1:ℂ),(u.2:ℂ)) := by sorry

theorem replacementCosh_fourier_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (θ : Fin 3 → ℝ) (x s : ℝ)
    (hx : 0 ≤ x) (hs : s ≤ 1) (hθ : ∀ j, |θ j| ≤ x)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (u : ℝ × ℝ) :
    ‖complexFourier (fun p => φ p*replacementCosh 1 θ p) ((u.1:ℂ),(u.2:ℂ))‖ ≤
      replacementDecayConstant*replacementP24 φ*x^2*(1+x)^22*Real.exp (2*s*x)/
        (1+max |u.1| |u.2|)^22 := by sorry

theorem replacementHeight_bounds (T : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T) :
    0 < T ∧ 0 < Real.log T ∧ 0 < meanSpacing T ∧
    0 ≤ Real.log (T/(2*Real.pi)) ∧ Real.log (T/(2*Real.pi)) ≤ Real.log T := by sorry

theorem replacementTuple_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (s T : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (v : ReplacementTriple) :
    ‖replacementTuple φ T v‖ ≤ replacementDecayConstant*replacementP24 φ*
      (replacementHorizontal T v)^2*(1+replacementHorizontal T v)^22*
      Real.exp (2*s*replacementHorizontal T v)/(1+replacementRadius T v)^22 := by sorry

theorem replacement_anchor_decay_summable (T a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (p : ℕ) (hp : 4 < p) (f : ReplacementTriple → ℂ)
    (hz : ∀ v, occurrenceOrdinate (v 0) ∉ Icc T (2*T) → f v=0)
    (hf : ∀ v, ‖f v‖ ≤ A/(1+max |(actualGaps a v).1| |(actualGaps a v).2|)^p) :
    Summable (fun v => ‖f v‖) := by sorry

theorem replacementWeight_bounds (w : ℝ → ℝ) (hw : TripleBudgetWeight w) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ u, |w u| ≤ W := by sorry

theorem replacementWeight_zero (w : ℝ → ℝ) (hw : TripleBudgetWeight w) (T : ℝ)
    (hT : 0 < T) (v : ReplacementTriple) (hv : occurrenceOrdinate (v 0) ∉ Icc T (2*T)) :
    w (occurrenceOrdinate (v 0)/T)=0 := by sorry

theorem replacementMomentTerm_nonneg (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (T s : ℝ) (hq : 0 ≤ Real.log T) (v : ReplacementTriple) :
    0 ≤ replacementMomentTerm w T s v := by sorry

theorem replacementMoment_summable (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (T s : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T) (hs : 0 < s) :
    Summable (replacementMomentTerm w T s) := by sorry

theorem replacementTuple_weighted_summable (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Summable (fun v => ‖(w (occurrenceOrdinate (v 0)/T):ℂ)*replacementTuple φ T v‖) := by sorry

theorem replacementKernel_global (v : ReplacementTriple) : ‖replacementKernel v‖ ≤ 7*Real.pi/9 := by sorry

theorem replacement_errors_summable (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Summable (fun v => ‖replacementTerm w φ T v‖) ∧
    Summable (fun v => ‖(w (occurrenceOrdinate (v 0)/T):ℂ)*kernelBenchmark*replacementTuple φ T v‖) ∧
    Summable (fun v => ‖(w (occurrenceOrdinate (v 0)/T):ℂ)*replacementKernel v*replacementTuple φ T v‖) := by sorry

theorem replacement_error_split (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    replacementEvenError w φ T = replacementConstantError w φ T+replacementError w φ T := by sorry

theorem replacement_absorb_decay (r x : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) :
    (r^2+x^2)*(1+x)^22/(1+r)^22 ≤ (1+x)^24/(1+r)^20 := by sorry

theorem replacement_large_height (T : ℝ) (hT : uniformHeightThreshold ≤ T) :
    2*Real.pi*Real.exp 1 ≤ T := by sorry

theorem replacementTerm_bound (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : uniformHeightThreshold ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (v : ReplacementTriple) :
    ‖replacementTerm w φ T v‖ ≤
      (replacementScaleConstant*replacementDecayConstant*replacementP24 φ/(Real.log T)^2)*
        replacementMomentTerm w T s v := by sorry

theorem replacementError_bound (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : uniformHeightThreshold ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    ‖replacementError w φ T‖ ≤
      ((16/3:ℝ)*replacementScaleConstant*replacementDecayConstant)*replacementP24 φ/
        (Real.log T)^2*replacementMoment w T s := by sorry

theorem replacementError_cutoff (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (16/(3*T*Real.log T):ℂ)*
      ∑ v ∈ tripleDomain S, replacementTerm w φ T v) atTop (𝓝 (replacementError w φ T)) := by sorry

theorem replacementTuple_zero_test (T : ℝ) (v : ReplacementTriple) :
    replacementTuple (fun _ => 0) T v=0 := by sorry

theorem replacementTuple_zero_displacement (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : ReplacementTriple)
    (hv : ∀ j, occurrenceDisplacement (v j)=0) : replacementTuple φ T v=0 := by sorry

theorem replacementError_zero_test (w : ℝ → ℝ) (T : ℝ) :
    replacementError w (fun _ => 0) T=0 := by sorry

theorem replacementMoment_nonneg (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (T s : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T) : 0 ≤ replacementMoment w T s := by sorry

theorem replacementKernel_equal_ordinates (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (v : ReplacementTriple) (h1 : occurrenceOrdinate (v 1)=occurrenceOrdinate (v 0))
    (h2 : occurrenceOrdinate (v 2)=occurrenceOrdinate (v 0)) :
    ‖replacementKernel v-kernelBenchmark‖ ≤ replacementScaleConstant*
      (replacementHorizontal T v)^2/(Real.log T)^2 := by sorry

theorem replacementKernel_height_endpoint (v : ReplacementTriple) :
    ‖replacementKernel v-kernelBenchmark‖ ≤ replacementScaleConstant*
      ((replacementRadius uniformHeightThreshold v)^2+(replacementHorizontal uniformHeightThreshold v)^2)/
        (Real.log uniformHeightThreshold)^2 := by sorry

theorem replacementTuple_height_endpoint (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (v : ReplacementTriple) :
    ‖replacementTuple φ (2*Real.pi*Real.exp 1) v‖ ≤ replacementDecayConstant*replacementP24 φ*
      (replacementHorizontal (2*Real.pi*Real.exp 1) v)^2*(1+replacementHorizontal (2*Real.pi*Real.exp 1) v)^22*
      Real.exp (2*s*replacementHorizontal (2*Real.pi*Real.exp 1) v)/
        (1+replacementRadius (2*Real.pi*Real.exp 1) v)^22 := by sorry

theorem replacementError_normalization (T : ℝ) :
    (16/(3*T*Real.log T):ℂ)*kernelBenchmark = (2*Real.pi/(T*Real.log T):ℂ) := by sorry

theorem replacementConstantError_cutoff (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (16/(3*T*Real.log T):ℂ)*
      ∑ v ∈ tripleDomain S, (w (occurrenceOrdinate (v 0)/T):ℂ)*kernelBenchmark*replacementTuple φ T v)
      atTop (𝓝 (replacementConstantError w φ T)) := by sorry

theorem replacementEvenError_cutoff (w : ℝ → ℝ) (hw : TripleBudgetWeight w)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (s T : ℝ) (hs : 0 < s) (hs1 : s < 1) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (16/(3*T*Real.log T):ℂ)*
      ∑ v ∈ tripleDomain S, (w (occurrenceOrdinate (v 0)/T):ℂ)*replacementKernel v*replacementTuple φ T v)
      atTop (𝓝 (replacementEvenError w φ T)) := by sorry

end
end HigherCorrelations
