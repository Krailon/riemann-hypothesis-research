import HigherCorrelations.SignedSectorDefinitions
import HigherCorrelations.SignedMasterIdentity
import HigherCorrelations.TripleTestPhase

/-! UNCONDITIONAL signed symmetries of the full occurrence sum. No subseries
invariance is asserted for the five equality-pattern pieces. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairZeroSeries_frequency_neg (B x t : ℝ) (hB : 0 < B) :
    pairZeroSeries (B^(-x),t)=star (pairZeroSeries (B^x,t)) := by
  rw [Real.rpow_neg hB.le,pairZeroSeries_reciprocal]

theorem tripleMasterProduct_three_frequencies (ω : ℝ → ℝ) (T B x y t : ℝ) (hB : 0 < B) :
    tripleMasterProduct ω T (B^x) (B^y) t =
      (ω (t/T)/T:ℝ)*pairZeroSeries (B^x,t)*pairZeroSeries (B^y,t)*pairZeroSeries (B^(-x-y),t) := by
  rw [tripleMasterProduct,← Real.rpow_add hB,show -x-y=-(x+y) by ring,
    pairZeroSeries_frequency_neg B (x+y) t hB]

theorem signedFrequency_rotation (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi < T) (p : ℝ × ℝ) :
    signedFrequency ω T (signedRotation p)=signedFrequency ω T p := by
  have hb : 0 < tripleTestBase T := by linarith [(tripleTestBase_bounds T hT).2.1]
  unfold signedFrequency tripleMasterObservable signedRotation
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleMasterProduct_three_frequencies ω T _ _ _ t hb,
    tripleMasterProduct_three_frequencies ω T _ _ _ t hb]
  rw [show -p.2-(-p.1-p.2)=p.1 by ring]
  ring

theorem signedFrequency_neg (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi < T) (p : ℝ × ℝ) :
    signedFrequency ω T (-p.1,-p.2)=star (signedFrequency ω T p) := by
  have hb : 0 < tripleTestBase T := by linarith [(tripleTestBase_bounds T hT).2.1]
  unfold signedFrequency tripleMasterObservable
  rw [Complex.star_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleMasterProduct_three_frequencies ω T _ _ _ t hb,
    tripleMasterProduct_three_frequencies ω T _ _ _ t hb]
  rw [show -(-p.1)-(-p.2)=-(-p.1-p.2) by ring]
  simp only [pairZeroSeries_frequency_neg _ _ _ hb,Complex.star_def,map_mul,Complex.conj_ofReal]

theorem signedFrequency_swap (ω : ℝ → ℝ) (T : ℝ) (p : ℝ × ℝ) :
    signedFrequency ω T p.swap=signedFrequency ω T p := by
  unfold signedFrequency tripleMasterObservable tripleMasterProduct
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Prod.fst_swap,Prod.snd_swap]
  rw [mul_comm ((tripleTestBase T)^p.2) ((tripleTestBase T)^p.1)]
  ring

theorem signedFrequency_sector (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi < T)
    (j : Fin 6) (p : ℝ × ℝ) :
    signedFrequency ω T (signedSector j p)=
      if j.val < 3 then signedFrequency ω T p else star (signedFrequency ω T p) := by
  have h1 := signedFrequency_rotation ω T hT p
  have h2 := (signedFrequency_rotation ω T hT (signedRotation p)).trans h1
  have hn := signedFrequency_neg ω T hT
  have hR : signedRotation (signedRotation p)=(-p.1-p.2,p.1) := by ext <;> simp [signedRotation] <;> ring
  rw [hR] at h2
  fin_cases j <;> norm_num [signedSector]
  · exact h1
  · exact h2
  · exact hn p
  · have hh := hn (signedRotation p)
    rw [h1] at hh
    simpa [signedRotation,add_comm] using hh
  · have hh := hn (-p.1-p.2,p.1)
    rw [h2] at hh
    simpa [add_comm] using hh

theorem signedFrequency_seam_real (ω : ℝ → ℝ) (T : ℝ) (hT : 2*Real.pi<T)
    (p : ℝ × ℝ) (hp : p ∈ signedSectorSeams) : star (signedFrequency ω T p)=signedFrequency ω T p := by
  have haxis (y : ℝ) : signedFrequency ω T (0,-y)=signedFrequency ω T (0,y) := by
    have h := signedFrequency_sector ω T hT 2 (0,y)
    norm_num [signedSector] at h
    exact (signedFrequency_swap ω T (-y,0)).trans h
  rw [← signedFrequency_neg ω T hT p]
  rcases hp with hx|hy|hz
  · rcases p with ⟨x,y⟩
    dsimp at hx ⊢
    subst x
    simpa using haxis y
  · rcases p with ⟨x,y⟩
    dsimp at hy ⊢
    subst y
    simpa using (signedFrequency_swap ω T (-x,0)).symm.trans ((haxis x).trans (signedFrequency_swap ω T (x,0)))
  · have hy : p.2 = -p.1 := by linarith
    simpa [Prod.swap,hy] using signedFrequency_swap ω T p

theorem tripleMasterProduct_signed_seam_real (ω : ℝ → ℝ) (T B : ℝ) (hB : 0<B)
    (p : ℝ × ℝ) (hp : p ∈ signedSectorSeams) (t : ℝ) :
    star (tripleMasterProduct ω T (B^p.1) (B^p.2) t) =
      tripleMasterProduct ω T (B^p.1) (B^p.2) t := by
  have hu : star (pairZeroSeries (1,t))=pairZeroSeries (1,t) := by
    simpa using (pairZeroSeries_reciprocal 1 t).symm
  simp only [Complex.star_def] at hu
  rw [tripleMasterProduct_three_frequencies ω T B p.1 p.2 t hB]
  rcases p with ⟨x,y⟩
  rcases hp with hx|hy|hz
  · dsimp at hx ⊢
    subst x
    simp only [neg_zero,zero_sub,Real.rpow_zero,pairZeroSeries_frequency_neg B y t hB,
      Complex.star_def,map_mul,Complex.conj_conj,Complex.conj_ofReal,hu]
    ring
  · dsimp at hy ⊢
    subst y
    simp only [sub_zero,Real.rpow_zero,pairZeroSeries_frequency_neg B x t hB,
      Complex.star_def,map_mul,Complex.conj_conj,Complex.conj_ofReal,hu]
    ring
  · have hy : y = -x := by change x+y=0 at hz; linarith
    subst y
    dsimp only
    rw [show -x- -x=0 by ring,Real.rpow_zero,pairZeroSeries_frequency_neg B x t hB]
    simp only [Complex.star_def,map_mul,Complex.conj_conj,Complex.conj_ofReal,hu]
    ring

end
end HigherCorrelations
