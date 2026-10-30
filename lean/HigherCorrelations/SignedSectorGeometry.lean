import HigherCorrelations.SignedSectorDefinitions
import HigherCorrelations.TripleQuadrantGeometry

/-! UNCONDITIONAL finite geometry of the six closed frequency cones. -/
namespace HigherCorrelations
noncomputable section
open Set

theorem signedSectorEquiv_apply (j : Fin 6) (p : ℝ × ℝ) : signedSectorEquiv j p=signedSector j p := rfl

theorem signedRotation_order_three (p : ℝ × ℝ) :
    signedRotation (signedRotation (signedRotation p))=p := by
  ext <;> simp [signedRotation] <;> ring

theorem signedSector_determinant (j : Fin 6) :
    (signedSector j (1,0)).1*(signedSector j (0,1)).2-
      (signedSector j (0,1)).1*(signedSector j (1,0)).2=1 := by
  fin_cases j <;> norm_num [signedSector]

theorem signedSector_image (j : Fin 6) : signedSector j '' tripleQuadrant=signedSectorCone j := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    fin_cases j <;> norm_num [signedSector,signedSectorCone,tripleQuadrant] at hq ⊢
    all_goals (try constructor) <;> linarith [hq.1,hq.2]
  · intro hp
    refine ⟨signedSector (signedSectorInverse j) p,?_,?_⟩
    · fin_cases j <;> simp [signedSectorCone] at hp <;>
        simp [signedSector,signedSectorInverse,tripleQuadrant] <;> constructor <;> linarith [hp.1,hp.2]
    · exact (signedSectorEquiv j).apply_symm_apply p

theorem signedSector_cover (p : ℝ × ℝ) : ∃ j : Fin 6, p ∈ signedSectorCone j := by
  by_cases hx : 0 ≤ p.1
  · by_cases hy : 0 ≤ p.2
    · exact ⟨0,hx,hy⟩
    · by_cases hz : p.1+p.2 ≤ 0
      · exact ⟨1,hx,hz⟩
      · exact ⟨5,by linarith,by linarith⟩
  · by_cases hy : p.2 ≤ 0
    · exact ⟨3,by linarith,hy⟩
    · by_cases hz : p.1+p.2 ≤ 0
      · exact ⟨2,by linarith,hz⟩
      · exact ⟨4,by linarith,by linarith⟩

set_option maxHeartbeats 800000 in
theorem signedSector_overlap (i j : Fin 6) (hij : i ≠ j) (p : ℝ × ℝ)
    (hi : p ∈ signedSectorCone i) (hj : p ∈ signedSectorCone j) : p ∈ signedSectorSeams := by
  by_contra hn
  have hne : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1+p.2 ≠ 0 := by simpa [signedSectorSeams,not_or] using hn
  fin_cases i <;> fin_cases j <;> simp [signedSectorCone] at hi hj hij
  all_goals rcases hi with ⟨hi1,hi2⟩; rcases hj with ⟨hj1,hj2⟩
  all_goals rcases lt_or_gt_of_ne hne.1 with hx|hx <;>
    rcases lt_or_gt_of_ne hne.2.1 with hy|hy <;>
    rcases lt_or_gt_of_ne hne.2.2 with hz|hz <;> linarith

theorem signedGauge_continuous : Continuous signedGauge := by unfold signedGauge; fun_prop

theorem signedGauge_nonneg (p : ℝ × ℝ) : 0 ≤ signedGauge p :=
  (abs_nonneg p.1).trans ((le_max_left _ _).trans (le_max_left _ _))

set_option maxHeartbeats 600000 in
theorem signedGauge_half_sum (p : ℝ × ℝ) :
    signedGauge p=(|p.1|+|p.2|+|p.1+p.2|)/2 := by
  unfold signedGauge
  simp only [abs_eq_max_neg,max_def]
  split_ifs <;> linarith

theorem signedGauge_sector (j : Fin 6) (p : ℝ × ℝ) (hp : p ∈ tripleQuadrant) :
    signedGauge (signedSector j p)=p.1+p.2 := by
  rw [signedGauge_half_sum]
  have hx := hp.1
  have hy := hp.2
  have hz : 0 ≤ p.1+p.2 := add_nonneg hx hy
  fin_cases j <;> simp [signedSector,abs_of_nonneg hx,abs_of_nonneg hy,abs_of_nonneg hz,
    abs_of_nonpos (show -p.1-p.2 ≤ 0 by linarith),
    abs_of_nonpos (show -p.2-p.1 ≤ 0 by linarith)] <;> ring
  all_goals simp only [abs_neg,abs_of_nonneg hy,abs_of_nonpos (show -p.1-p.2 ≤ 0 by linarith)]
  all_goals ring

end
end HigherCorrelations
