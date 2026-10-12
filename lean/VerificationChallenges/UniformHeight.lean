import HigherCorrelations.UniformHeightDefinitions
import HigherCorrelations.IntegralProfileDefinitions
import Mathlib.Analysis.Complex.JensenFormula

/-! Definition-only specifications. Intentional unfinished proofs for Comparator;
solution modules never import this file. -/
namespace HigherCorrelations
noncomputable section
open Metric Complex Real
open scoped Classical

theorem zeta_norm_le_quarter_strip {z : ℂ} (h1 : 1 / 4 ≤ z.re) (him : 1 ≤ |z.im|) :
    ‖riemannZeta z‖ ≤ 3 + 2 * ‖z‖ := by sorry

theorem zeta_line_two_lower (t : ℝ) : (1/4 : ℝ) ≤ ‖riemannZeta (2 + I*t)‖ := by sorry

theorem stripZero_interval_finite (v w : ℝ) :
    Set.Finite {ρ : StripZero | v ≤ ρ.val.im ∧ ρ.val.im ≤ w} := by sorry

theorem mem_stripZeroInterval (v w : ℝ) (ρ : StripZero) :
    ρ ∈ stripZeroInterval v w ↔ v ≤ ρ.val.im ∧ ρ.val.im ≤ w := by sorry

theorem mem_occurrenceInterval (v w : ℝ) (i : ZeroOccurrence) :
    i ∈ occurrenceInterval v w ↔ v ≤ occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ w := by sorry

theorem occurrenceInterval_card (v w : ℝ) :
    (occurrenceInterval v w).card = ∑ ρ ∈ stripZeroInterval v w, zeroMultiplicity ρ := by sorry

theorem occurrenceInterval_subset_cutoff (v w : ℝ) :
    occurrenceInterval v w ⊆ occurrenceCutoff (max |v| |w|) := by sorry

theorem occurrenceInterval_mono {v w v' w' : ℝ} (hv : v' ≤ v) (hw : w ≤ w') :
    occurrenceInterval v w ⊆ occurrenceInterval v' w' := by sorry

theorem occurrenceInterval_empty {v w : ℝ} (h : w < v) : occurrenceInterval v w = ∅ := by sorry

theorem rightStripZeroInterval_mem (v w : ℝ) (ρ : StripZero) :
    ρ ∈ rightStripZeroInterval v w ↔ v ≤ ρ.val.im ∧ ρ.val.im ≤ w ∧ 1/2 ≤ ρ.val.re := by sorry

theorem occurrenceInterval_card_le_twice_right (v w : ℝ) :
    (occurrenceInterval v w).card ≤ 2 * ∑ ρ ∈ rightStripZeroInterval v w, zeroMultiplicity ρ := by sorry

theorem jensen_disk_geometry (t : ℝ) (ht : 4 ≤ |t|) (z : ℂ)
    (hz : z ∈ closedBall (jensenCenter t) (7/4)) :
    1/4 ≤ z.re ∧ 1 ≤ |z.im| ∧ ‖z‖ ≤ |t| + 4 := by sorry

theorem jensen_disk_analytic (t : ℝ) (ht : 4 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (jensenCenter t) (7/4)) := by sorry

theorem jensen_disk_norm_bound (t : ℝ) (ht : 4 ≤ |t|) (z : ℂ)
    (hz : z ∈ closedBall (jensenCenter t) (7/4)) :
    ‖riemannZeta z‖ ≤ 16*(|t|+2) := by sorry

theorem localJensenMass_bound (t : ℝ) (ht : 4 ≤ |t|) :
    localJensenMass t ≤ (7 / Real.log (35/32)) * Real.log (|t|+2) := by sorry

theorem right_interval_in_jensen_disk (v : ℝ) (ρ : StripZero)
    (hρ : ρ ∈ rightStripZeroInterval v (v+1)) :
    ρ.val ∈ closedBall (jensenCenter (v+1/2)) (8/5) := by sorry

theorem right_interval_mass_le_jensen (v : ℝ) (hv : 4 ≤ |v+1/2|) :
    (∑ ρ ∈ rightStripZeroInterval v (v+1), (zeroMultiplicity ρ : ℝ)) ≤
      localJensenMass (v+1/2) := by sorry

theorem occurrence_unit_count_high (v : ℝ) (hv : 4 ≤ |v+1/2|) :
    ((occurrenceInterval v (v+1)).card : ℝ) ≤
      (28 / Real.log (35/32))*Real.log (|v|+2) := by sorry

theorem occurrence_unit_count_low (v : ℝ) (hv : |v+1/2| < 4) :
    (occurrenceInterval v (v+1)).card ≤ (occurrenceCutoff 5).card := by sorry

theorem occurrence_count_local :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
      ((occurrenceInterval v (v+1)).card : ℝ) ≤ C*Real.log (|v|+2) := by sorry

theorem occurrence_interval_unit_cover (v w : ℝ) (_hvw : v ≤ w) :
    occurrenceInterval v w ⊆ (Finset.range (⌊w-v⌋₊+1)).biUnion
      (fun n => occurrenceInterval (v+n) (v+n+1)) := by sorry

theorem occurrence_count_interval :
    ∃ C : ℝ, 0 < C ∧ ∀ v w : ℝ, v ≤ w →
      ((occurrenceInterval v w).card : ℝ) ≤
        C*(w-v+1)*Real.log (max |v| |w|+2) := by sorry

theorem occurrenceCutoff_eq_interval (U : ℝ) :
    occurrenceCutoff U = occurrenceInterval (-U) U := by sorry

theorem occurrence_count_logarithmic :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 0 ≤ U →
      ((occurrenceCutoff U).card : ℝ) ≤ C*(U+1)*Real.log (U+2) := by sorry

theorem occurrence_count_centered :
    ∃ C : ℝ, 0 < C ∧ ∀ t r : ℝ, 0 ≤ r →
      ((occurrenceInterval (t-r) (t+r)).card:ℝ) ≤ C*(1+r)*Real.log (|t|+r+2) := by sorry

theorem kernelTailRadius_nonneg (t a : ℝ) (ha : 0 ≤ a) (i : KernelTailOccurrence t a) :
    0 ≤ kernelTailRadius t a i := by sorry

theorem kernelTailRadius_identity (t a : ℝ) (ha : 0 ≤ a) (i : KernelTailOccurrence t a) :
    (1+a)*(1+kernelTailRadius t a i) = 1+|t-occurrenceOrdinate i.val| := by sorry

theorem kernelTail_shell_upper (t a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (i : KernelTailOccurrence t a) (hi : dyadicIndex (kernelTailRadius t a i) = n) :
    |t-occurrenceOrdinate i.val| ≤ (1+a)*2^(n+1) := by sorry

theorem kernelTail_shell_finite (t a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Set.Finite {i : KernelTailOccurrence t a | dyadicIndex (kernelTailRadius t a i) = n} := by sorry

theorem kernelTail_shell_log (t a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Real.log (|t|+(1+a)*2^(n+1)+2) ≤ ((n:ℝ)+3)*Real.log (|t|+a+2) := by sorry

theorem ordinateKernel_nonneg (x : ℝ) : 0 ≤ ordinateKernel x := by sorry

theorem ordinateKernel_quadratic (x : ℝ) : ordinateKernel x ≤ 2/(1+|x|)^2 := by sorry

theorem kernel_geometric_hasSum :
    HasSum (fun n : ℕ => ((n:ℝ)+3)*(1/2:ℝ)^n) 8 := by sorry

theorem zeroKernelTail_summable_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t a : ℝ, ∀ _ha : 0 ≤ a,
      Summable (fun i : KernelTailOccurrence t a => ordinateKernel (t-occurrenceOrdinate i.val)) ∧
      zeroKernelTail t a ≤ C*Real.log (|t|+a+2)/(1+a) := by sorry

theorem zeroKernel_summable_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Summable (fun i : ZeroOccurrence => ordinateKernel (t-occurrenceOrdinate i)) ∧
      zeroKernelSum t ≤ C*Real.log (|t|+2) := by sorry

theorem kernel_restricted_le_tail (t a : ℝ) (ha : 0 ≤ a) (P : ZeroOccurrence → Prop)
    (hP : ∀ i, P i → a ≤ |t-occurrenceOrdinate i|) :
    Summable (fun i : {i // P i} => ordinateKernel (t-occurrenceOrdinate i.val)) ∧
    (∑' i : {i // P i}, ordinateKernel (t-occurrenceOrdinate i.val)) ≤ zeroKernelTail t a := by sorry

theorem zeroKernel_distant_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T Z t : ℝ, 3 ≤ T → 2*T ≤ Z → 0 ≤ t → t ≤ T →
      (∑' i : {i : ZeroOccurrence // Z < |occurrenceOrdinate i|}, ordinateKernel (t-occurrenceOrdinate i.val)) ≤
        C*Real.log Z/Z := by sorry

theorem zeroKernel_exterior_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T t : ℝ, 0 ≤ T → 0 ≤ t → t ≤ T →
      (∑' i : {i : ZeroOccurrence // occurrenceOrdinate i ≤ 0 ∨ T < occurrenceOrdinate i},
        ordinateKernel (t-occurrenceOrdinate i.val)) ≤
        C*Real.log (T+2)*(1/(1+t)+1/(1+T-t)) := by sorry

theorem heightIntervalDistance_geometry (T t : ℝ) (hT : 0 ≤ T) (ht : t ≤ 0 ∨ T ≤ t) :
    0 ≤ heightIntervalDistance T t ∧ |t| ≤ T+heightIntervalDistance T t ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ T → heightIntervalDistance T t ≤ |t-x| := by sorry

theorem zeroKernel_interior_finite (T t : ℝ) :
    (∑' i : {i : ZeroOccurrence // 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T},
      ordinateKernel (t-occurrenceOrdinate i.val)) ≤
      ∑ i ∈ occurrenceInterval 0 T, ordinateKernel (t-occurrenceOrdinate i) := by sorry

theorem zeroKernel_interior_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T t : ℝ, 3 ≤ T → (t ≤ 0 ∨ T ≤ t) →
      (∑' i : {i : ZeroOccurrence // 0 < occurrenceOrdinate i ∧ occurrenceOrdinate i ≤ T},
        ordinateKernel (t-occurrenceOrdinate i.val)) ≤
        C*Real.log (T+2)/(1+heightIntervalDistance T t) := by sorry

theorem uniformHeightThreshold_bounds {T : ℝ} (hT : uniformHeightThreshold ≤ T) :
    3 ≤ T ∧ 1 ≤ Real.log T ∧ 1 ≤ meanSpacing T := by sorry

theorem height_radius_log_bound (T R : ℝ) (hT : 3 ≤ T) (hq : 1 ≤ Real.log T) (hR : 0 ≤ R) :
    Real.log (2*T+R+2) ≤ 3*(1+R)*Real.log T := by sorry

theorem anchoredBall_finite (T a R : ℝ) (ha : 0 < a) :
    Set.Finite {t : AnchoredTriple T | anchoredRadius T a t ≤ R} := by sorry

theorem mem_anchoredBall (T a R : ℝ) (ha : 0 < a) (t : AnchoredTriple T) :
    t ∈ anchoredBall T a R ↔ anchoredRadius T a t ≤ R := by sorry

theorem anchored_count_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ T a R : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ R →
      ((anchoredBall T a R).card:ℝ) ≤ C*T*(Real.log T)^3*(1+R)^4 := by sorry

theorem project_anchored_count_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ T R : ℝ, uniformHeightThreshold ≤ T → 0 ≤ R →
      ((anchoredBall T (meanSpacing T) R).card:ℝ) ≤ C*T*(Real.log T)^3*(1+R)^4 := by sorry

theorem anchoredTailRadius_nonneg (T a R : ℝ) (hR : 0 ≤ R) (t : AnchoredTail T a R) :
    0 ≤ anchoredTailRadius T a R t := by sorry

theorem anchoredTailRadius_identity (T a R : ℝ) (hR : 0 ≤ R) (t : AnchoredTail T a R) :
    (1+R)*(1+anchoredTailRadius T a R t) = 1+anchoredRadius T a t.val := by sorry

theorem anchoredTail_shell_upper (T a R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (t : AnchoredTail T a R) (ht : dyadicIndex (anchoredTailRadius T a R t) = n) :
    anchoredRadius T a t.val ≤ (1+R)*2^(n+1) := by sorry

theorem anchoredTail_shell_finite (T a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) (n : ℕ) :
    Set.Finite {t : AnchoredTail T a R | dyadicIndex (anchoredTailRadius T a R t) = n} := by sorry

theorem dyadic_total_bound {I : Type*} (S : OccurrenceShells I) (f : I → ℂ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (d p : ℕ) (hp : d<p)
    (hc : ∀ n, ((S.members n).card:ℝ) ≤ C*((2:ℝ)^d)^n)
    (hf : ∀ i, ‖f i‖ ≤ A/((2:ℝ)^p)^S.shell i) :
    Summable (fun i => ‖f i‖) ∧ (∑' i, ‖f i‖) ≤ A*C/(1-dyadicRatio d p) := by sorry

theorem anchored_decay_tail_uniform (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a R A : ℝ, uniformHeightThreshold ≤ T →
      1 ≤ a → 0 ≤ R → 0 ≤ A → ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      Summable (fun t : AnchoredTail T a R => ‖f t.val‖) ∧
      (∑' t : AnchoredTail T a R, ‖f t.val‖)/(T*Real.log T) ≤
        C*A*(Real.log T)^2/(1+R)^(p-4) := by sorry

theorem anchored_decay_mass_uniform (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T →
      1 ≤ a → 0 ≤ A → ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      Summable (fun t => ‖f t‖) ∧ normalizedTripleMass T f ≤ C*A*(Real.log T)^2 := by sorry

theorem anchored_decay_strict_tail_uniform (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a R A : ℝ, uniformHeightThreshold ≤ T →
      1 ≤ a → 0 ≤ R → 0 ≤ A → ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      normalizedTripleTail T a R f ≤ C*A*(Real.log T)^2/(1+R)^(p-4) := by sorry

theorem bounded_factor_decay {I : Type*} (r : I → ℝ) (f k : I → ℂ) (A B : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ)
    (hk : ∀ i, ‖k i‖ ≤ B) (hf : ∀ i, ‖f i‖ ≤ A/(1+r i)^p) :
    ∀ i, ‖k i*f i‖ ≤ (B*A)/(1+r i)^p := by sorry

theorem weighted_real_test_decay (T a W A : ℝ) (hW : 0 ≤ W) (_hA : 0 ≤ A) (p : ℕ)
    (w : ℝ → ℂ) (F : ℝ × ℝ → ℂ)
    (hw : ∀ x, T ≤ x → x ≤ 2*T → ‖w x‖ ≤ W)
    (hF : ∀ u v : ℝ, ‖F (u,v)‖ ≤ A/(1+max |u| |v|)^p) :
    ∀ t : AnchoredTriple T,
      ‖w (occurrenceOrdinate t.1.val)*F
        (a*(occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val),
         a*(occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val))‖ ≤
        (W*A)/(1+anchoredRadius T a t)^p := by sorry

theorem project_weighted_mass_tail (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T W A : ℝ, uniformHeightThreshold ≤ T → 0 ≤ W → 0 ≤ A →
      ∀ w : ℝ → ℂ, ∀ F : ℝ × ℝ → ℂ,
      (∀ x, T ≤ x → x ≤ 2*T → ‖w x‖ ≤ W) →
      (∀ u v, ‖F (u,v)‖ ≤ A/(1+max |u| |v|)^p) →
      let f : AnchoredTriple T → ℂ := fun t => w (occurrenceOrdinate t.1.val)*F
        (meanSpacing T*(occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val),
         meanSpacing T*(occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val))
      Summable (fun t => ‖f t‖) ∧ normalizedTripleMass T f ≤ C*W*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 1 ≤ R → normalizedTripleTail T (meanSpacing T) R f ≤
        C*W*A*(Real.log T)^2/R^(p-4) := by sorry

theorem anchored_decay_twentieth_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ A →
      ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^20) →
      normalizedTripleTail T a ((Real.log T)^(1/4:ℝ)) f ≤ C*A/(Real.log T)^2 := by sorry

theorem bounded_multiplier_mass_tail (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A B : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a →
      0 ≤ A → 0 ≤ B → ∀ f k : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) → (∀ t, ‖k t‖ ≤ B) →
      Summable (fun t => ‖k t*f t‖) ∧
      normalizedTripleMass T (fun t => k t*f t) ≤ C*B*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 0 ≤ R → normalizedTripleTail T a R (fun t => k t*f t) ≤
        C*B*A*(Real.log T)^2/(1+R)^(p-4) := by sorry

theorem actual_kernel_uniform_bounds (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ A →
      ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      let g := fun t => actualRationalKernel (anchoredToTriple t)*f t
      Summable (fun t => ‖g t‖) ∧ normalizedTripleMass T g ≤ C*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 0 ≤ R → normalizedTripleTail T a R g ≤ C*A*(Real.log T)^2/(1+R)^(p-4) := by sorry

theorem actual_horizontal_uniform_bounds (js : List (Fin 3)) (p : ℕ) (hp : 4<p) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a A : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ A →
      ∀ f : AnchoredTriple T → ℂ,
      (∀ t, ‖f t‖ ≤ A/(1+anchoredRadius T a t)^p) →
      let g := fun t => horizontalPartial js
        (horizontalProfile (actualProfileGap (anchoredToTriple t) 1) (actualProfileGap (anchoredToTriple t) 2))
        (actualProfileParameters (anchoredToTriple t))*f t
      Summable (fun t => ‖g t‖) ∧ normalizedTripleMass T g ≤ C*A*(Real.log T)^2 ∧
      ∀ R : ℝ, 0 ≤ R → normalizedTripleTail T a R g ≤ C*A*(Real.log T)^2/(1+R)^(p-4) := by sorry

theorem meanSpacing_log_comparison {T : ℝ} (hT : uniformHeightThreshold ≤ T) :
    Real.log T ≤ 4*Real.pi*meanSpacing T := by sorry

theorem transferCoefficient_mass_bound (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (f : AnchoredTriple T → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    ‖transferCoefficient T*(∑' t, f t)‖ ≤ (16/3)*normalizedTripleMass T f := by sorry

theorem ordinateCoefficient_mass_bound (T : ℝ) (hT : uniformHeightThreshold ≤ T)
    (f : AnchoredTriple T → ℂ) (hf : Summable (fun t => ‖f t‖)) :
    ‖ordinateCoefficient T*(∑' t, f t)‖ ≤ (4*Real.pi)*normalizedTripleMass T f := by sorry

end
end HigherCorrelations
