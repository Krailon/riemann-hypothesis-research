import HigherCorrelations.FiniteReflection
import HigherCorrelations.FiniteSigns
import HigherCorrelations.ZeroReflection

/-! UNCONDITIONAL finite checks; the explicit configurations are SYNTHETIC_MODEL.
These are exact kernel-checked examples, not assertions about actual zeta zeros.
-/
namespace HigherCorrelations

theorem example_five_patterns :
    classifyTriple ![0, 0, 0] = .allEqual ∧
    classifyTriple ![0, 0, 1] = .only01 ∧
    classifyTriple ![0, 1, 0] = .only02 ∧
    classifyTriple ![0, 1, 1] = .only12 ∧
    classifyTriple ![0, 1, 2] = .allDistinct := by decide

theorem example_empty_domain :
    (tripleDomain ![∅, {0, 1}, {2, 3}] : Finset (Fin 3 → ℕ)).card = 0 := by decide

theorem example_singleton_domain :
    (tripleDomain ![{0}, {1}, {2}] : Finset (Fin 3 → ℕ)).card = 1 := by decide

theorem example_different_cutoffs :
    (tripleDomain ![{0}, {0, 1}, {2, 3, 4}] : Finset (Fin 3 → ℕ)).card = 6 := by decide

theorem example_repeated_occurrences :
    (∑ i : Fin 3, (![2, 2, 5] : Fin 3 → ℕ) i) = 9 ∧
    (∑ a ∈ (Finset.univ : Finset (Fin 3)).image (![0, 0, 1] : Fin 3 → ℕ),
      if a = 0 then 2 else 5) = 7 ∧
    ((Finset.univ : Finset (Fin 3)).filter (fun i => (![0, 0, 1] : Fin 3 → ℕ) i = 0)).card = 2 := by
  decide

theorem example_distinct_complex_same_ordinate :
    let t : Fin 3 → ℂ := ![(1 / 4 : ℂ) + 3 * Complex.I, (3 / 4 : ℂ) + 3 * Complex.I,
      (1 / 4 : ℂ) + 3 * Complex.I]
    classifyTriple (Complex.im ∘ t) = .allEqual ∧ classifyTriple t = .only02 := by
  norm_num [classifyTriple, Function.comp_def, Complex.ext_iff]

theorem example_fixed_point (y : ℝ) :
    horizontalReflection ((1 / 2 : ℂ) + y * Complex.I) = (1 / 2 : ℂ) + y * Complex.I := by
  apply Complex.ext <;> norm_num [horizontalReflection]

theorem example_exchanged_pair :
    horizontalReflection ((1 / 4 : ℂ) + 3 * Complex.I) = (3 / 4 : ℂ) + 3 * Complex.I := by
  apply Complex.ext <;> norm_num [horizontalReflection]

end HigherCorrelations
