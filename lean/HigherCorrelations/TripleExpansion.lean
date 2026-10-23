import HigherCorrelations.TripleExpansionDefinitions
import HigherCorrelations.TripleMasterPatterns
import HigherCorrelations.PairRHSContinuity

/-! UNCONDITIONAL exact ordered 27-word expansion. Only finite distributivity
and integration are performed here; prime-series Fourier interchange is separate. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

private def letterSign (l : MasterLetter) : ℤ := if l = .P then -1 else 1

theorem tripleWordSign_product (w : MasterWord) :
    tripleWordSign w = ∏ r : Fin 3, (if w r = .P then (-1:ℤ) else 1) := by
  simp only [tripleWordSign, tripleWordPrimeCount, Fin.sum_univ_three,
    Fin.prod_univ_three, pow_add]
  simp

/-- The exact four remainders are retained even at unit base and negative t. -/
theorem tripleComponent_remainder (X t : ℝ) :
    tripleComponent .H X t = pairArchError (X,t)+pairDSError (X,t)+
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by
  exact pairRHS_remainder_sum X t

theorem tripleComponent_explicit_formula (X t : ℝ) (hX : 1≤X) :
    pairZeroSeries (X,t) = -tripleComponent .P X t + tripleComponent .A X t +
      tripleComponent .H X t := by
  rw [tripleComponent_remainder, pairUniform_formula X t hX]
  simp only [tripleComponent, tripleArch]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem tripleComponent_continuous (l : MasterLetter) (X : ℝ) (hX : 1≤X) :
    Continuous (tripleComponent l X) := by
  cases l
  · exact pairRHS_prime_continuous X hX
  · unfold tripleComponent tripleArch
    exact Complex.continuous_ofReal.comp
      (((continuous_abs.add_const 2).log (fun t => by positivity)).div_const X)
  · unfold tripleComponent pairRHSRemainderSum
    exact continuous_finsetSum _ (fun j _ => pairRHS_remainder_continuous j X hX)

theorem tripleSmoothedIntegral_normalization (ω : ℝ → ℝ) (T : ℝ) (f g h : ℝ → ℂ) :
    tripleSmoothedIntegral ω T f g h = (1/(T:ℂ))*
      ∫ t : ℝ, (ω (t/T):ℂ)*f t*g t*star (h t) := by
  unfold tripleSmoothedIntegral tripleSmoothedIntegrand
  rw [← integral_const_mul]
  congr 1
  funext t
  push_cast
  ring

theorem tripleWordIntegrand_continuous (ω : ℝ → ℝ) (hω : Continuous ω)
    (T X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord) :
    Continuous (tripleWordIntegrand ω T X Y w) := by
  have hXY : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  unfold tripleWordIntegrand tripleSmoothedIntegrand
  exact (((Complex.continuous_ofReal.comp ((hω.comp (continuous_id.div_const T)).div_const T)).mul
    (tripleComponent_continuous _ _ hX)).mul (tripleComponent_continuous _ _ hY)).mul
      (tripleComponent_continuous _ _ hXY).star

theorem tripleWordIntegrand_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord) :
    Integrable (tripleWordIntegrand ω T X Y w) := by
  apply (tripleWordIntegrand_continuous ω hω T X Y hX hY w).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply tripleMaster_support ω hs T hT
  intro hz
  exact ht (by simp [tripleWordIntegrand,tripleSmoothedIntegrand,hz])

/-- Pure complex algebra, including conjugation of the third slot and its sign. -/
theorem tripleWord_algebra (F : Fin 3 → MasterLetter → ℂ) :
    (-F 0 .P+F 0 .A+F 0 .H)*(-F 1 .P+F 1 .A+F 1 .H)*
      star (-F 2 .P+F 2 .A+F 2 .H) =
    ∑ w : MasterWord, (tripleWordSign w:ℂ)*
      (F 0 (w 0)*F 1 (w 1)*star (F 2 (w 2))) := by
  classical
  let f : Fin 3 → MasterLetter → ℂ := fun r l =>
    if r = 2 then star ((letterSign l : ℂ)*F r l) else (letterSign l : ℂ)*F r l
  have hp := Finset.prod_univ_sum (fun _ : Fin 3 => Finset.univ) f
  have hu : Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset MasterLetter)) = Finset.univ := by
    ext w
    simp
  rw [hu, Fin.prod_univ_three] at hp
  have hl (r : Fin 3) : (∑ l : MasterLetter, (letterSign l:ℂ)*F r l) =
      -F r .P+F r .A+F r .H := by
    rw [show (Finset.univ : Finset MasterLetter) = {.P,.A,.H} from rfl]
    simp [letterSign, add_assoc]
  have hsum : ∑ l : MasterLetter, f 2 l = star (-F 2 .P+F 2 .A+F 2 .H) := by
    simp only [f, if_pos rfl, ← star_sum, hl]
  have h0 : ∑ l : MasterLetter, f 0 l = -F 0 .P+F 0 .A+F 0 .H := by
    simpa only [f, show (0:Fin 3) ≠ 2 by decide, if_false] using hl 0
  have h1 : ∑ l : MasterLetter, f 1 l = -F 1 .P+F 1 .A+F 1 .H := by
    simpa only [f, show (1:Fin 3) ≠ 2 by decide, if_false] using hl 1
  rw [h0,h1,hsum] at hp
  rw [hp]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fin.prod_univ_three, tripleWordSign_product, Fin.prod_univ_three]
  simp only [f, letterSign, show (0:Fin 3) ≠ 2 by decide,
    show (1:Fin 3) ≠ 2 by decide, if_false, if_pos rfl, Int.cast_mul, star_mul,
    star_intCast]
  ring

theorem tripleMasterProduct_word_expansion (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    tripleMasterProduct ω T X Y t =
      ∑ w : MasterWord, (tripleWordSign w:ℂ)*tripleWordIntegrand ω T X Y w t := by
  have hXY : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have h := tripleWord_algebra (fun r l =>
    tripleComponent l (if r = 0 then X else if r = 1 then Y else X*Y) t)
  simp only [show (1:Fin 3) ≠ 0 by decide, show (2:Fin 3) ≠ 0 by decide,
    show (2:Fin 3) ≠ 1 by decide, ↓reduceIte] at h
  unfold tripleMasterProduct
  rw [tripleComponent_explicit_formula X t hX, tripleComponent_explicit_formula Y t hY,
    tripleComponent_explicit_formula (X*Y) t hXY]
  calc
    _ = (ω (t/T)/T:ℝ)*
        ((-tripleComponent .P X t+tripleComponent .A X t+tripleComponent .H X t)*
         (-tripleComponent .P Y t+tripleComponent .A Y t+tripleComponent .H Y t)*
         star (-tripleComponent .P (X*Y) t+tripleComponent .A (X*Y) t+tripleComponent .H (X*Y) t)) := by ring
    _ = _ := by
      rw [h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp [tripleWordIntegrand,tripleSmoothedIntegrand]
      ring

theorem tripleMaster_word_expansion (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      ∑ w : MasterWord, (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w := by
  unfold tripleMasterObservable
  simp_rw [tripleMasterProduct_word_expansion ω T X Y hX hY]
  rw [integral_finsetSum _ (fun w _ =>
    (tripleWordIntegrand_integrable ω hω hs T X Y (by linarith) hX hY w).const_mul _)]
  simp only [integral_const_mul, tripleWordIntegral]

/-- All 27 words occur once in the explicit P,A,H enumeration. -/
theorem tripleWordTable_nodup : (tripleWordTable.map Prod.fst).Nodup := by decide

theorem tripleWordTable_complete : (tripleWordTable.map Prod.fst).toFinset =
    (Finset.univ : Finset MasterWord) := by decide

/-- Every recorded sign and remainder flag agrees with its mathematical definition. -/
theorem tripleWordTable_correct : ∀ row ∈ tripleWordTable,
    row.2.1 = tripleWordSign row.1 ∧ row.2.2 = tripleWordHasH row.1 := by decide

theorem tripleWord_counts : Fintype.card MasterWord = 27 ∧
    (Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = false)).card = 8 ∧
    (Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = true)).card = 19 := by decide

/-- Direct connection to the literal ordered table, including its recorded signs. -/
theorem tripleMaster_table_expansion (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      (tripleWordTable.map (fun row => (row.2.1:ℂ)*tripleWordIntegral ω T X Y row.1)).sum := by
  rw [tripleMaster_word_expansion ω hω hs T X Y hT hX hY,
    ← tripleWordTable_complete, List.sum_toFinset _ tripleWordTable_nodup, List.map_map]
  congr 1

/-- Eight words without H plus nineteen with H, all retained exactly. -/
theorem tripleMaster_word_split (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      (∑ w ∈ Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = false),
        (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w) +
      (∑ w ∈ Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = true),
        (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w) := by
  rw [tripleMaster_word_expansion ω hω hs T X Y hT hX hY]
  symm
  simpa using Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w : MasterWord => tripleWordHasH w = false)
    (fun w => (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w)

/-- The unit bases still supply actual prime/archimedean/remainder functions. -/
theorem tripleMaster_word_minimal (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    tripleMasterObservable ω 3 1 1 =
      ∑ w : MasterWord, (tripleWordSign w:ℂ)*tripleWordIntegral ω 3 1 1 w :=
  tripleMaster_word_expansion ω hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num)

theorem tripleWordIntegral_zero_weight (T X Y : ℝ) (w : MasterWord) :
    tripleWordIntegral (fun _ => 0) T X Y w = 0 := by
  simp [tripleWordIntegral,tripleWordIntegrand,tripleSmoothedIntegrand]

theorem tripleWordIntegral_neg_weight (ω : ℝ → ℝ) (T X Y : ℝ) (w : MasterWord) :
    tripleWordIntegral (fun t => -ω t) T X Y w = -tripleWordIntegral ω T X Y w := by
  simp [tripleWordIntegral,tripleWordIntegrand,tripleSmoothedIntegrand,neg_div,integral_neg]

end
end HigherCorrelations
