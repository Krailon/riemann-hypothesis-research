import HigherCorrelations.IntervalZeroCounting
import HigherCorrelations.ZeroOccurrenceShells
import HigherCorrelations.UniformHeightDefinitions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! UNCONDITIONAL uniform global counts. No pair-correlation estimate is used. -/
namespace HigherCorrelations
noncomputable section

theorem uniformHeightThreshold_bounds {T : ℝ} (hT : uniformHeightThreshold ≤ T) :
    3 ≤ T ∧ 1 ≤ Real.log T ∧ 1 ≤ meanSpacing T := by
  have hp := Real.pi_gt_three
  have he : 1 ≤ Real.exp (2*Real.pi) := Real.one_le_exp (by positivity)
  have ht : 3 ≤ T := by unfold uniformHeightThreshold at hT; nlinarith
  have hq : 2*Real.pi ≤ Real.log (T/(2*Real.pi)) := by
    have h := Real.log_le_log (Real.exp_pos (2*Real.pi))
      ((le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by simpa [uniformHeightThreshold, mul_comm] using hT))
    simpa using h
  have hm : 1 ≤ meanSpacing T := (le_div_iff₀ (by positivity)).mpr (by simpa using hq)
  have hl : Real.log (T/(2*Real.pi)) ≤ Real.log T := Real.log_le_log (by positivity)
    ((div_le_self (by linarith) (by linarith)))
  exact ⟨ht,by linarith,hm⟩

theorem height_radius_log_bound (T R : ℝ) (hT : 3 ≤ T) (hq : 1 ≤ Real.log T) (hR : 0 ≤ R) :
    Real.log (2*T+R+2) ≤ 3*(1+R)*Real.log T := by
  have hh : 2*T+R+2 ≤ T^2*(1+R) := by
    nlinarith [mul_nonneg (show 0 ≤ T^2-1 by nlinarith) hR]
  have hl := Real.log_le_log (by positivity) hh
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
  norm_num at hl
  have hr := Real.log_le_sub_one_of_pos (show 0 < 1+R by positivity)
  nlinarith [mul_nonneg hR (sub_nonneg.mpr hq),mul_nonneg hR (show 0 ≤ Real.log T by linarith)]

theorem anchor_card_eq_interval (T : ℝ) :
    Fintype.card (AnchorOccurrence T) = (occurrenceInterval T (2*T)).card := by
  classical
  let e : AnchorOccurrence T ≃ {i // i ∈ occurrenceInterval T (2*T)} :=
    { toFun := fun i => ⟨i.val,(mem_occurrenceInterval _ _ _).mpr i.property⟩
      invFun := fun i => ⟨i.val,(mem_occurrenceInterval _ _ _).mp i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

theorem anchoredBall_finite (T a R : ℝ) (ha : 0 < a) :
    Set.Finite {t : AnchoredTriple T | anchoredRadius T a t ≤ R} := by
  apply ((Set.finite_univ : (Set.univ : Set (AnchorOccurrence T)).Finite).prod
    ((occurrence_height_finite (2*|T|+|R|/a)).prod
      (occurrence_height_finite (2*|T|+|R|/a)))).subset
  intro t ht
  change anchoredRadius T a t ≤ R at ht
  refine ⟨Set.mem_univ _, ?_, ?_⟩ <;>
    change |occurrenceOrdinate _| ≤ 2*|T|+|R|/a
  all_goals
    have h₁ : |a*(occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val)| ≤ R := (le_max_left _ _).trans ht
    have h₂ : |a*(occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val)| ≤ R := (le_max_right _ _).trans ht
    rw [abs_mul,abs_of_pos ha] at h₁ h₂
    have hi : |occurrenceOrdinate t.1.val| ≤ 2*|T| := abs_le.mpr
      ⟨by linarith [t.1.property.1,neg_abs_le T,abs_nonneg T], by linarith [t.1.property.2,le_abs_self T]⟩
    have hh₁ := (le_div_iff₀ ha).mpr (show |occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val| *a ≤ R by linarith)
    have hh₂ := (le_div_iff₀ ha).mpr (show |occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val| *a ≤ R by linarith)
    have hr : R/a ≤ |R|/a := div_le_div_of_nonneg_right (le_abs_self R) ha.le
    have hs (i : ZeroOccurrence) : |occurrenceOrdinate i| ≤
        |occurrenceOrdinate i-occurrenceOrdinate t.1.val|+|occurrenceOrdinate t.1.val| := by
      simpa using abs_add_le (occurrenceOrdinate i-occurrenceOrdinate t.1.val) (occurrenceOrdinate t.1.val)
    first
    | exact (hs t.2.1).trans (by linarith)
    | exact (hs t.2.2).trans (by linarith)

theorem mem_anchoredBall (T a R : ℝ) (ha : 0 < a) (t : AnchoredTriple T) :
    t ∈ anchoredBall T a R ↔ anchoredRadius T a t ≤ R := by
  classical
  simp [anchoredBall,anchoredBall_finite T a R ha]

theorem anchoredBall_cover (T a R : ℝ) (ha : 1 ≤ a) :
    anchoredBall T a R ⊆ Finset.univ.biUnion (fun i : AnchorOccurrence T =>
      {i} ×ˢ (occurrenceInterval (occurrenceOrdinate i.val-R) (occurrenceOrdinate i.val+R) ×ˢ
        occurrenceInterval (occurrenceOrdinate i.val-R) (occurrenceOrdinate i.val+R))) := by
  classical
  intro t ht
  have h := (mem_anchoredBall T a R (by linarith) t).mp ht
  have h₁ : |occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val| ≤ R := by
    have hh : |a*(occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val)| ≤ R := (le_max_left _ _).trans h
    rw [abs_mul,abs_of_pos (by linarith : 0<a)] at hh
    nlinarith [abs_nonneg (occurrenceOrdinate t.2.1-occurrenceOrdinate t.1.val)]
  have h₂ : |occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val| ≤ R := by
    have hh : |a*(occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val)| ≤ R := (le_max_right _ _).trans h
    rw [abs_mul,abs_of_pos (by linarith : 0<a)] at hh
    nlinarith [abs_nonneg (occurrenceOrdinate t.2.2-occurrenceOrdinate t.1.val)]
  refine Finset.mem_biUnion.mpr ⟨t.1,Finset.mem_univ _,?_⟩
  simp only [Finset.mem_product,Finset.mem_singleton,mem_occurrenceInterval,true_and]
  exact ⟨⟨by linarith [(abs_le.mp h₁).1],by linarith [(abs_le.mp h₁).2]⟩,
    ⟨by linarith [(abs_le.mp h₂).1],by linarith [(abs_le.mp h₂).2]⟩⟩

theorem anchored_count_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ T a R : ℝ, uniformHeightThreshold ≤ T → 1 ≤ a → 0 ≤ R →
      ((anchoredBall T a R).card:ℝ) ≤ C*T*(Real.log T)^3*(1+R)^4 := by
  classical
  obtain ⟨C,hC,hb⟩ := occurrence_count_centered
  refine ⟨27*C^3,by positivity,fun T a R hT ha hR => ?_⟩
  obtain ⟨ht,hq,hm⟩ := uniformHeightThreshold_bounds hT
  have ht0 : 0 ≤ T := by linarith
  have hq0 : 0 ≤ Real.log T := by linarith
  have hanchor : (Fintype.card (AnchorOccurrence T):ℝ) ≤ 3*C*T*Real.log T := by
    rw [anchor_card_eq_interval]
    have hh := hb (3*T/2) (T/2) (by positivity)
    have hl := height_radius_log_bound T 0 ht hq (by norm_num)
    norm_num at hl
    have he₁ : 3*T/2-T/2=T := by ring
    have he₂ : 3*T/2+T/2=2*T := by ring
    rw [he₁,he₂,abs_of_nonneg (by positivity),he₂] at hh
    calc
      _ ≤ C*(1+T/2)*(3*Real.log T) := hh.trans (mul_le_mul_of_nonneg_left hl (by positivity))
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC.le hq0) (show 0 ≤ T/2-1 by linarith)]
  have hpartner (i : AnchorOccurrence T) :
      ((occurrenceInterval (occurrenceOrdinate i.val-R) (occurrenceOrdinate i.val+R)).card:ℝ) ≤
        3*C*(1+R)^2*Real.log T := by
    have hi : 0 ≤ occurrenceOrdinate i.val := ht0.trans i.property.1
    have hl := Real.log_le_log (show 0 < |occurrenceOrdinate i.val|+R+2 by positivity)
      (show |occurrenceOrdinate i.val|+R+2 ≤ 2*T+R+2 by rw [abs_of_nonneg hi]; linarith [i.property.2])
    have hh := (hb (occurrenceOrdinate i.val) R hR).trans
      (mul_le_mul_of_nonneg_left (hl.trans (height_radius_log_bound T R ht hq hR)) (by positivity))
    convert hh using 1 <;> ring
  have hc : ((anchoredBall T a R).card:ℝ) ≤ ∑ i : AnchorOccurrence T,
      ((occurrenceInterval (occurrenceOrdinate i.val-R) (occurrenceOrdinate i.val+R)).card:ℝ)^2 := by
    have hh := (Finset.card_le_card (anchoredBall_cover T a R ha)).trans Finset.card_biUnion_le
    simpa only [Finset.card_product,Finset.card_singleton,one_mul,← pow_two,Nat.cast_sum,Nat.cast_pow] using (Nat.cast_le (α:=ℝ)).mpr hh
  calc
    _ ≤ (Fintype.card (AnchorOccurrence T):ℝ)*(3*C*(1+R)^2*Real.log T)^2 := by
      apply hc.trans
      calc
        _ ≤ ∑ _i : AnchorOccurrence T, (3*C*(1+R)^2*Real.log T)^2 := by
          apply Finset.sum_le_sum; intro i _; exact pow_le_pow_left₀ (by positivity) (hpartner i) 2
        _ = _ := by simp
    _ ≤ (3*C*T*Real.log T)*(3*C*(1+R)^2*Real.log T)^2 := mul_le_mul_of_nonneg_right hanchor (sq_nonneg _)
    _ = _ := by ring

theorem project_anchored_count_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ T R : ℝ, uniformHeightThreshold ≤ T → 0 ≤ R →
      ((anchoredBall T (meanSpacing T) R).card:ℝ) ≤ C*T*(Real.log T)^3*(1+R)^4 := by
  obtain ⟨C,hC,hb⟩ := anchored_count_uniform
  exact ⟨C,hC,fun T R hT hR => hb T _ R hT (uniformHeightThreshold_bounds hT).2.2 hR⟩

end
end HigherCorrelations
