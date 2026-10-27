import HigherCorrelations.TripleTestDefinitions
import HigherCorrelations.TripleInteriorVanishing
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! UNCONDITIONAL compact support margins and local-spacing range conversion. -/
namespace HigherCorrelations
noncomputable section
open Set Filter
open scoped Topology

theorem tripleTestMargin_subset (ε : ℝ) (hε : 0 < ε) : tripleTestMargin ε ⊆ tripleTestRegion := by
  rintro p ⟨hx,hy,hz⟩
  exact ⟨lt_of_lt_of_le hε hx,lt_of_lt_of_le hε hy,by linarith⟩

theorem tripleTest_compact_margin (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hs : K ⊆ tripleTestRegion) : ∃ ε : ℝ, 0 < ε ∧ ε < 1/3 ∧ K ⊆ tripleTestMargin ε := by
  by_cases hn : K.Nonempty
  · let f : ℝ × ℝ → ℝ := fun p => min p.1 (min p.2 (1-p.1-p.2))
    have hf : Continuous f := by unfold f; fun_prop
    obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hn hf.continuousOn
    obtain ⟨hp1,hp2,hp3⟩ := hs hp
    have hfp : 0 < f p := by dsimp [f]; exact lt_min hp1 (lt_min hp2 (by linarith))
    refine ⟨min (f p/2) (1/4),lt_min (by linarith) (by norm_num),?_,?_⟩
    · exact (min_le_right _ _).trans_lt (by norm_num)
    · intro q hq
      have hh : min (f p/2) (1/4) ≤ f q := (min_le_left _ _).trans ((by linarith : f p/2 ≤ f p).trans (hmin hq))
      have h1 := hh.trans (min_le_left _ _)
      have h2 := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
      have h3 := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
      exact ⟨h1,h2,by dsimp [f] at h3; linarith⟩
  · refine ⟨1/4,by norm_num,by norm_num,?_⟩
    simpa [Set.not_nonempty_iff_eq_empty.mp hn]

theorem tripleTestBase_bounds (T : ℝ) (hT : 2*Real.pi < T) :
    3 ≤ T ∧ 1 < tripleTestBase T ∧ tripleTestBase T ≤ T := by
  have hp := Real.pi_gt_three
  have hp0 : 0 < 2*Real.pi := by positivity
  refine ⟨by linarith,?_,?_⟩
  · exact (lt_div_iff₀ hp0).mpr (by simpa using hT)
  · exact div_le_self (by linarith) (by linarith)

theorem tripleTest_scale_range (ε T : ℝ) (p : ℝ × ℝ) (hε : 0 < ε)
    (hT : 2*Real.pi < T) (hp : p ∈ tripleTestMargin ε) :
    1 ≤ (tripleTestBase T)^ε ∧
    (tripleTestBase T)^ε ≤ (tripleTestBase T)^p.1 ∧
    (tripleTestBase T)^ε ≤ (tripleTestBase T)^p.2 ∧
    (tripleTestBase T)^p.1*(tripleTestBase T)^p.2 ≤ (tripleTestBase T)^(1-ε) ∧
    (tripleTestBase T)^p.1*(tripleTestBase T)^p.2 ≤ T/(tripleTestBase T)^ε := by
  obtain ⟨ht,hb,hbt⟩ := tripleTestBase_bounds T hT
  have hb0 : 0 < tripleTestBase T := by linarith
  have hz : (tripleTestBase T)^p.1*(tripleTestBase T)^p.2 ≤ (tripleTestBase T)^(1-ε) := by
    rw [← Real.rpow_add hb0]
    exact Real.rpow_le_rpow_of_exponent_le hb.le hp.2.2
  refine ⟨Real.one_le_rpow hb.le hε.le,Real.rpow_le_rpow_of_exponent_le hb.le hp.1,
    Real.rpow_le_rpow_of_exponent_le hb.le hp.2.1,hz,?_⟩
  apply hz.trans
  rw [Real.rpow_sub hb0,Real.rpow_one]
  exact div_le_div_of_nonneg_right hbt (Real.rpow_nonneg hb0.le _)

end
end HigherCorrelations
