import HigherCorrelations.TripleTestAsymptotic
import HigherCorrelations.ComplexFourierRegularity
import Mathlib.MeasureTheory.Integral.Prod

/-! UNCONDITIONAL zero test, nonempty class, and coordinate exchange checks. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleTest_zero (ω : ℝ → ℝ) (T : ℝ) : tripleTestStatistic ω (fun _ => 0) T=0 := by
  simp [tripleTestStatistic,complexFourier]

theorem tripleTest_margin_exchange (ε : ℝ) (p : ℝ × ℝ) :
    p.swap ∈ tripleTestMargin ε ↔ p ∈ tripleTestMargin ε := by
  simp only [tripleTestMargin,Set.mem_setOf_eq,Prod.fst_swap,Prod.snd_swap]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h2,h1,by linarith⟩

theorem tripleTest_frequency_exchange (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    (∫ p : ℝ × ℝ, φ p.swap*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)) =
    ∫ p : ℝ × ℝ, φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) := by
  have hh := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ => φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2))
  simpa only [Measure.volume_eq_prod,Prod.fst_swap,Prod.snd_swap,tripleMasterObservable_swap ω T] using hh

/-- A smooth nonzero test supported inside the manuscript's explicit square. -/
theorem tripleTest_nonempty : ∃ φ : ℝ × ℝ → ℂ,
    ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ φ (1/4,1/4)=1 ∧
    tsupport φ ⊆ Icc (3/16:ℝ) (5/16) ×ˢ Icc (3/16:ℝ) (5/16) ∧
    tsupport φ ⊆ tripleTestMargin (1/8) := by
  let s := Ioo (3/16:ℝ) (5/16) ×ˢ Ioo (3/16:ℝ) (5/16)
  have hopen : IsOpen s := isOpen_Ioo.prod isOpen_Ioo
  have hx : ((1/4,1/4):ℝ × ℝ) ∈ s := by norm_num [s]
  obtain ⟨f,hs,hc,hf,hr,hxval⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hopen.mem_nhds hx)
  have he : tsupport (fun p => (f p:ℂ))=tsupport f := by
    unfold tsupport
    congr 1
    ext p
    simp [Function.mem_support]
  refine ⟨fun p => (f p:ℂ),Complex.ofRealCLM.contDiff.comp hf,?_,?_,?_,?_⟩
  · change IsCompact (tsupport (fun p => (f p:ℂ)))
    rw [he]
    exact hc
  · exact congrArg Complex.ofReal hxval
  · rw [he]
    intro p hp
    obtain ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ := hs hp
    exact ⟨⟨h1.le,h2.le⟩,⟨h3.le,h4.le⟩⟩
  · rw [he]
    intro p hp
    obtain ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ := hs hp
    exact ⟨by linarith,by linarith,by linarith⟩

end
end HigherCorrelations
