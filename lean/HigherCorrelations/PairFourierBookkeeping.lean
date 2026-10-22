import HigherCorrelations.PairFourierIdentity
import HigherCorrelations.FinitePatterns

/-! UNCONDITIONAL finite occurrence bookkeeping. Equal ordinates are never used
as a substitute for equal occurrences or equal complex zeros. -/
namespace HigherCorrelations
noncomputable section

theorem pairFrequencyTerm_horizontal (T a : ℝ) (i j : ZeroOccurrence) :
    pairFrequencyTerm T a i j =
      4*Complex.exp ((a*(pairHorizontalCoordinate T i-pairHorizontalCoordinate T j) : ℝ) +
        Complex.I*(a*(occurrenceOrdinate i-occurrenceOrdinate j)*Real.log T : ℝ)) /
      (4-((occurrenceValue i).re-(occurrenceValue j).re : ℂ)^2+
        (occurrenceOrdinate i-occurrenceOrdinate j : ℂ)^2-
        2*Complex.I*((occurrenceValue i).re-(occurrenceValue j).re : ℂ)*
          (occurrenceOrdinate i-occurrenceOrdinate j : ℂ)) := by
  have he : (a*Real.log T : ℝ)*(occurrenceValue i-occurrenceValue j) =
      (a*(pairHorizontalCoordinate T i-pairHorizontalCoordinate T j) : ℝ) +
        Complex.I*(a*(occurrenceOrdinate i-occurrenceOrdinate j)*Real.log T : ℝ) := by
    apply Complex.ext <;> simp [pairHorizontalCoordinate,occurrenceDisplacement,occurrenceOrdinate] <;> ring
  have hd : 4-(occurrenceValue i-occurrenceValue j)^2 =
      4-((occurrenceValue i).re-(occurrenceValue j).re : ℂ)^2+
        (occurrenceOrdinate i-occurrenceOrdinate j : ℂ)^2-
        2*Complex.I*((occurrenceValue i).re-(occurrenceValue j).re : ℂ)*
          (occurrenceOrdinate i-occurrenceOrdinate j : ℂ) := by
    apply Complex.ext <;> simp [occurrenceOrdinate,Complex.mul_re,Complex.mul_im,pow_two] <;> ring
  unfold pairFrequencyTerm pairDifferenceWeight
  rw [he,hd]
  ring

theorem pairFrequencyTerm_diagonal (T a : ℝ) (i j : ZeroOccurrence)
    (h : occurrenceValue i = occurrenceValue j) : pairFrequencyTerm T a i j = 1 := by
  simp [pairFrequencyTerm,pairDifferenceWeight,h]

theorem pairFrequencyTerm_index_diagonal (T a : ℝ) :
    (∑ i ∈ occurrenceWindow 0 T, pairFrequencyTerm T a i i) =
      ((occurrenceWindow 0 T).card : ℂ) := by
  simp [pairFrequencyTerm_diagonal]

theorem pairWindow_fiber_card (T : ℝ) (ρ : StripZero) (hρ : 0<ρ.val.im ∧ ρ.val.im≤T) :
    ((occurrenceWindow 0 T).filter (fun i => i.1=ρ)).card = zeroMultiplicity ρ := by
  classical
  have he : (occurrenceWindow 0 T).filter (fun i => i.1=ρ) =
      (Finset.univ : Finset (Fin (zeroMultiplicity ρ))).map ⟨fun k => ⟨ρ,k⟩, by
        intro a b hab; exact Sigma.mk.inj_iff.mp hab |>.2 |> eq_of_heq⟩ := by
    ext i
    constructor
    · intro hi
      have h := (Finset.mem_filter.mp hi).2
      obtain ⟨τ,k⟩ := i
      dsimp at h
      subst τ
      exact Finset.mem_map.mpr ⟨k,Finset.mem_univ _,rfl⟩
    · intro hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_filter.mpr ⟨(mem_occurrenceWindow _ _ _).mpr hρ,rfl⟩
  rw [he,Finset.card_map,Finset.card_univ,Fintype.card_fin]

theorem pairFrequencyTerm_equal_zero_diagonal (T a : ℝ) :
    (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ (occurrenceWindow 0 T).filter
        (fun j => occurrenceValue j = occurrenceValue i), pairFrequencyTerm T a i j) =
      ∑ ρ ∈ (occurrenceWindow 0 T).image (fun i => i.1), (zeroMultiplicity ρ : ℂ)^2 := by
  classical
  have hf (i : ZeroOccurrence) :
      (occurrenceWindow 0 T).filter (fun j => occurrenceValue j=occurrenceValue i) =
      (occurrenceWindow 0 T).filter (fun j => j.1=i.1) := by
    ext j
    simp only [Finset.mem_filter,and_congr_right_iff]
    intro _
    exact Subtype.val_inj
  have hi (i : ZeroOccurrence) (hi : i ∈ occurrenceWindow 0 T) :
      (∑ j ∈ (occurrenceWindow 0 T).filter (fun j => occurrenceValue j=occurrenceValue i),
        pairFrequencyTerm T a i j) = (zeroMultiplicity i.1 : ℂ) := by
    calc
      _ = ∑ _j ∈ (occurrenceWindow 0 T).filter (fun j => occurrenceValue j=occurrenceValue i), (1:ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact pairFrequencyTerm_diagonal T a i j (Finset.mem_filter.mp hj).2.symm
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hf,
        pairWindow_fiber_card T i.1 ((mem_occurrenceWindow _ _ _).mp hi)]
  rw [Finset.sum_congr rfl hi,sum_regroup_multiplicity (occurrenceWindow 0 T) (fun i => i.1) (fun ρ => (zeroMultiplicity ρ : ℂ))]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hρ
  rw [pairWindow_fiber_card T i.1 ((mem_occurrenceWindow _ _ _).mp hi)]
  simp [pow_two]

theorem pairFrequencyTerm_reflection (T a : ℝ) :
    (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T, pairFrequencyTerm T a i j) =
      ∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
        Complex.exp ((a*Real.log T : ℝ)*(occurrenceValue i+star (occurrenceValue j)-1))*
          pairDifferenceWeight (occurrenceValue i+star (occurrenceValue j)-1) := by
  classical
  symm
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_bij (fun j _ => occurrenceReflection j)
  · intro j hj; exact (pairZeroWindow_reflection T j).mpr hj
  · intro j hj k hk h; exact occurrenceReflection_involutive.injective h
  · intro j hj
    exact ⟨occurrenceReflection j,(pairZeroWindow_reflection T j).mpr hj,
      occurrenceReflection_involutive j⟩
  · intro j hj
    unfold pairFrequencyTerm
    rw [occurrenceReflection_value]
    unfold horizontalReflection
    simp only [Complex.star_def]
    congr 2 <;> ring

end
end HigherCorrelations
