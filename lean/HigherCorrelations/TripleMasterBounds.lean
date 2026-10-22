import HigherCorrelations.TripleMasterDefinitions
import HigherCorrelations.PairZeroConvergence
import HigherCorrelations.OccurrenceIntegration

/-! UNCONDITIONAL dominating function for the triple master integrand.
Finite sums are bounded first; integral-norm summability is proved afterwards. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleMasterTerm_continuous (ω : ℝ → ℝ) (hω : Continuous ω)
    (T X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (v : MasterTriple) :
    Continuous (tripleMasterTerm ω T X Y v) := by
  have hc (i : ZeroOccurrence) (Z : ℝ) (hZ : 1≤Z) :
      Continuous (fun t : ℝ => pairZeroTerm i (Z,t)) :=
    (pairZeroTerm_continuous i).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => hZ)
  have hXY : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  unfold tripleMasterTerm
  exact (((Complex.continuous_ofReal.comp ((hω.comp (continuous_id.div_const T)).div_const T)).mul
    (hc _ _ hX)).mul (hc _ _ hY)).mul (hc _ _ hXY).star

theorem tripleMaster_support (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) :
    Function.support (fun t : ℝ => ω (t/T)) ⊆ Icc T (2*T) := by
  intro t ht
  have hh := hs ht
  exact ⟨by simpa using (le_div_iff₀ hT).mp hh.1,(div_le_iff₀ hT).mp hh.2⟩

theorem tripleMaster_weight_compact (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) :
    HasCompactSupport (fun t : ℝ => ω (t/T)) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (tripleMaster_support ω hs T hT)

theorem tripleMasterTerm_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) (v : MasterTriple) :
    Integrable (tripleMasterTerm ω T X Y v) := by
  apply (tripleMasterTerm_continuous ω hω T X Y hX hY v).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply tripleMaster_support ω hs T hT
  intro hz
  exact ht (by simp [tripleMasterTerm,hz])

theorem tripleMaster_weight_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ => |ω (t/T)|/T) := by
  exact (((hω.comp (continuous_id.div_const T)).integrable_of_hasCompactSupport
    (tripleMaster_weight_compact ω hs T hT)).norm).div_const T

theorem tripleMaster_weight_mass (ω : ℝ → ℝ) (T : ℝ) (hT : 0<T) :
    (∫ t : ℝ, |ω (t/T)|/T) = ∫ u : ℝ, |ω u| := by
  rw [integral_div,Measure.integral_comp_div (fun u => |ω u|) T,abs_of_pos hT,smul_eq_mul]
  field_simp

theorem tripleMasterMajorant_integrable (C₀ : ℝ) (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ) (hT : 0<T) :
    Integrable (tripleMasterMajorant C₀ ω T X Y) :=
  (tripleMaster_weight_integrable ω hω hs T hT).const_mul _

theorem tripleMasterMajorant_integral (C₀ : ℝ) (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T) :
    (∫ t : ℝ, tripleMasterMajorant C₀ ω T X Y t) = tripleMasterL1Bound C₀ ω T X Y := by
  unfold tripleMasterMajorant tripleMasterL1Bound
  rw [integral_const_mul,tripleMaster_weight_mass ω T hT]

theorem tripleMasterTerm_bound (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T)
    (hX : 1≤X) (hY : 1≤Y) (v : MasterTriple) (t : ℝ) :
    ‖tripleMasterTerm ω T X Y v t‖ ≤
      ((8/3 : ℝ)^3*X*Y*(|ω (t/T)|/T))*
        ∏ r : Fin 3, ordinateKernel (t-occurrenceOrdinate (v r)) := by
  have hx : 0≤X := by linarith
  have hy : 0≤Y := by linarith
  have hXY : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have h0 := pairZeroTerm_bound (v 0) X t hX
  have h1 := pairZeroTerm_bound (v 1) Y t hY
  have h2 := pairZeroTerm_bound (v 2) (X*Y) t hXY
  have hsqrt : Real.sqrt X*Real.sqrt Y*Real.sqrt (X*Y) = X*Y := by
    rw [Real.sqrt_mul hx]
    nlinarith [Real.sq_sqrt hx,Real.sq_sqrt hy]
  unfold tripleMasterTerm
  simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hT]
  have hk0 := ordinateKernel_nonneg (t-occurrenceOrdinate (v 0))
  have hk1 := ordinateKernel_nonneg (t-occurrenceOrdinate (v 1))
  have hk2 := ordinateKernel_nonneg (t-occurrenceOrdinate (v 2))
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul h0 h1 (norm_nonneg _) (by positivity)) h2
      (norm_nonneg _) (by positivity)) (div_nonneg (abs_nonneg (ω (t/T))) hT.le)
  calc
    _ = (|ω (t/T)|/T)*(‖pairZeroTerm (v 0) (X,t)‖*‖pairZeroTerm (v 1) (Y,t)‖*
        ‖pairZeroTerm (v 2) (X*Y,t)‖) := by ring
    _ ≤ _ := hb
    _ = _ := by
      rw [Fin.prod_univ_three]
      calc
        _ = ((8/3 : ℝ)^3*(Real.sqrt X*Real.sqrt Y*Real.sqrt (X*Y))*(|ω (t/T)|/T))*
          (ordinateKernel (t-occurrenceOrdinate (v 0))*ordinateKernel (t-occurrenceOrdinate (v 1))*
          ordinateKernel (t-occurrenceOrdinate (v 2))) := by ring
        _ = _ := by rw [hsqrt]; ring

theorem tripleMaster_finite_kernel (D : Finset MasterTriple) (t : ℝ) :
    (∑ v ∈ D, ∏ r : Fin 3, ordinateKernel (t-occurrenceOrdinate (v r))) ≤ (zeroKernelSum t)^3 := by
  classical
  let s := D.biUnion (fun v => Finset.univ.image v)
  have hsub : D ⊆ Fintype.piFinset (fun _ : Fin 3 => s) := by
    intro v hv
    rw [Fintype.mem_piFinset]
    intro r
    exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩⟩
  have hs : (∑ i ∈ s, ordinateKernel (t-occurrenceOrdinate i)) ≤ zeroKernelSum t :=
    (zeroKernel_summable_bound.choose_spec.2 t).1.sum_le_tsum s
      (fun i _ => ordinateKernel_nonneg _)
  calc
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => s), ∏ r : Fin 3, ordinateKernel (t-occurrenceOrdinate (v r)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Finset.prod_nonneg (fun _ _ => ordinateKernel_nonneg _))
    _ = (∑ i ∈ s, ordinateKernel (t-occurrenceOrdinate i))^3 := by
      rw [Finset.sum_prod_piFinset s (fun (_ : Fin 3) i => ordinateKernel (t-occurrenceOrdinate i))]
      simp
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => ordinateKernel_nonneg _)) hs 3

theorem tripleMaster_finite_majorant (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y)
    (D : Finset MasterTriple) (t : ℝ) :
    (∑ v ∈ D, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterMajorant C₀ ω T X Y t := by
  have ht : 0<T := by linarith
  by_cases hz : ω (t/T)=0
  · simp [tripleMasterTerm,tripleMasterMajorant,hz]
  have hh := tripleMaster_support ω hs T ht hz
  have hlog : Real.log (|t|+2) ≤ Real.log (2*T+2) := by
    rw [abs_of_nonneg (by linarith [hh.1] : 0≤t)]
    exact Real.log_le_log (by linarith [hh.1]) (by linarith [hh.2])
  have hq : 0≤zeroKernelSum t := tsum_nonneg (fun i => ordinateKernel_nonneg _)
  have hb : zeroKernelSum t ≤ C₀*Real.log (2*T+2) :=
    (hQ t).trans (mul_le_mul_of_nonneg_left hlog hC₀)
  have hc : 0≤(8/3:ℝ)^3*X*Y*(|ω (t/T)|/T) := by positivity
  calc
    _ ≤ ∑ v ∈ D, ((8/3:ℝ)^3*X*Y*(|ω (t/T)|/T))*
        ∏ r : Fin 3, ordinateKernel (t-occurrenceOrdinate (v r)) :=
      Finset.sum_le_sum (fun v _ => tripleMasterTerm_bound ω T X Y ht hX hY v t)
    _ = ((8/3:ℝ)^3*X*Y*(|ω (t/T)|/T))*
        (∑ v ∈ D, ∏ r : Fin 3, ordinateKernel (t-occurrenceOrdinate (v r))) := by rw [Finset.mul_sum]
    _ ≤ ((8/3:ℝ)^3*X*Y*(|ω (t/T)|/T))*(zeroKernelSum t)^3 :=
      mul_le_mul_of_nonneg_left (tripleMaster_finite_kernel D t) hc
    _ ≤ ((8/3:ℝ)^3*X*Y*(|ω (t/T)|/T))*(C₀*Real.log (2*T+2))^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hb 3) hc
    _ = _ := by unfold tripleMasterMajorant; ring

theorem tripleMaster_finite_integralNorm_bound (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : Continuous ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (D : Finset MasterTriple) :
    (∑ v ∈ D, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterL1Bound C₀ ω T X Y := by
  have ht : 0<T := by linarith
  have hi (v : MasterTriple) := (tripleMasterTerm_integrable ω hω hs T X Y ht hX hY v).norm
  rw [← integral_finsetSum _ (fun v _ => hi v),← tripleMasterMajorant_integral C₀ ω T X Y ht]
  exact integral_mono (integrable_finsetSum _ (fun v _ => hi v))
    (tripleMasterMajorant_integrable C₀ ω hω hs T X Y ht)
    (tripleMaster_finite_majorant C₀ hC₀ hQ ω hs T X Y hT hX hY D)

theorem tripleMaster_integralNorm_bound (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : Continuous ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ∧
    (∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterL1Bound C₀ ω T X Y := by
  have hn (v : MasterTriple) : 0≤∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hb := tripleMaster_finite_integralNorm_bound C₀ hC₀ hQ ω hω hs T X Y hT hX hY
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

theorem tripleMaster_uniform_integralNorm :
    ∃ C₀ : ℝ, 0<C₀ ∧ (∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2)) ∧
      ∀ (ω : ℝ → ℝ), Continuous ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T X Y : ℝ, 3≤T → 1≤X → 1≤Y →
      Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ∧
      (∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterL1Bound C₀ ω T X Y := by
  obtain ⟨C₀,hC₀,hQ⟩ := zeroKernel_summable_bound
  exact ⟨C₀,hC₀,fun t => (hQ t).2,fun ω hω hs T X Y hT hX hY =>
    tripleMaster_integralNorm_bound C₀ hC₀.le (fun t => (hQ t).2) ω hω hs T X Y hT hX hY⟩

end
end HigherCorrelations
