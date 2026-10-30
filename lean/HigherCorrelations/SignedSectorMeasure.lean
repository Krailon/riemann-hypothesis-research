import HigherCorrelations.SignedSectorGeometry
import HigherCorrelations.TripleQuadrantGeometry
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! UNCONDITIONAL measure-preserving sector changes and null seams. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem signedSector_measurePreserving (j : Fin 6) :
    MeasurePreserving (signedSector j) volume volume := by
  have h5 : MeasurePreserving (signedSector 5) volume volume := by
    change MeasurePreserving (fun p : ℝ × ℝ => (p.1+p.2,-p.1)) volume volume
    simpa [Measure.volume_eq_prod,add_comm] using
      (measurePreserving_add_prod_neg (volume : Measure ℝ) (volume : Measure ℝ))
  have h1 : MeasurePreserving (signedSector 1) volume volume := by
    convert h5.comp h5 using 1
    ext p <;> simp [signedSector,Function.comp_def] <;> ring
  have h2 : MeasurePreserving (signedSector 2) volume volume := by
    convert h1.comp h1 using 1
    ext p <;> simp [signedSector,Function.comp_def] <;> ring
  have h3 : MeasurePreserving (signedSector 3) volume volume := by
    convert h5.comp h1 using 1
    ext p <;> simp [signedSector,Function.comp_def] <;> ring
  have h4 : MeasurePreserving (signedSector 4) volume volume := by
    convert h3.comp h1 using 1
    ext p <;> simp [signedSector,Function.comp_def] <;> ring
  fin_cases j
  · exact MeasurePreserving.id _
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem signedSector_measurable (j : Fin 6) : MeasurableSet (signedSectorCone j) := by
  rw [← signedSector_image]
  exact (signedSectorEquiv j).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    tripleQuadrant_measurable

theorem signedSector_integral (j : Fin 6) (f : ℝ × ℝ → ℂ) :
    (∫ p in signedSectorCone j, f p) = ∫ p in tripleQuadrant, f (signedSector j p) := by
  rw [← signedSector_image]
  exact (signedSector_measurePreserving j).setIntegral_image_emb
    (signedSectorEquiv j).toHomeomorph.measurableEmbedding f tripleQuadrant

theorem signedSector_seams_null : volume signedSectorSeams = 0 := by
  have h0 : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
  have hx : volume {p : ℝ × ℝ | p.1=0} = 0 := by
    rw [show {p : ℝ × ℝ | p.1=0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) by ext p; simp]
    simp [Measure.volume_eq_prod,h0]
  have hy : volume {p : ℝ × ℝ | p.2=0} = 0 := by
    rw [show {p : ℝ × ℝ | p.2=0} = (univ : Set ℝ) ×ˢ ({0} : Set ℝ) by ext p; simp]
    simp [Measure.volume_eq_prod,h0]
  have hz : volume {p : ℝ × ℝ | p.1+p.2=0} = 0 := by
    have hh := (signedSector_measurePreserving 5).measure_preimage
      (show MeasurableSet {p : ℝ × ℝ | p.1=0} from isClosed_eq continuous_fst continuous_const |>.measurableSet).nullMeasurableSet
    rw [hx] at hh
    exact hh
  exact measure_union_null hx (measure_union_null hy hz)

theorem signedSector_partition_integral (f : ℝ × ℝ → ℂ) (hf : Integrable f) :
    (∫ p, f p) = ∑ j : Fin 6, ∫ p in tripleQuadrant, f (signedSector j p) := by
  classical
  have hn : ∀ᵐ p : ℝ × ℝ, p ∉ signedSectorSeams := by
    rw [ae_iff]
    simpa using signedSector_seams_null
  have he : (fun p => ∑ j : Fin 6, (signedSectorCone j).indicator f p) =ᵐ[volume] f := by
    filter_upwards [hn] with p hp
    obtain ⟨j,hj⟩ := signedSector_cover p
    rw [Finset.sum_eq_single j]
    · exact indicator_of_mem hj f
    · intro k _ hkj
      apply indicator_of_notMem
      intro hk
      exact hp (signedSector_overlap k j hkj p hk hj)
    · simp
  rw [← integral_congr_ae he,integral_finset_sum _ (fun j _ => hf.indicator (signedSector_measurable j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (signedSector_measurable j),signedSector_integral]

theorem signedSector_disjoint_interiors (i j : Fin 6) (hij : i ≠ j) :
    Disjoint (interior (signedSectorCone i)) (interior (signedSectorCone j)) := by
  apply disjoint_iff_inter_eq_empty.mpr
  apply (isOpen_interior.inter isOpen_interior).eq_empty_of_measure_zero (μ := volume)
  exact measure_mono_null (fun p hp => signedSector_overlap i j hij p
    (interior_subset hp.1) (interior_subset hp.2)) signedSector_seams_null

end
end HigherCorrelations
