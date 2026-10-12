import HigherCorrelations.ProfileTaylor

/-! UNCONDITIONAL profile identity and derivative bounds for actual zero occurrences.
All ordered tuples, signs, multiplicities and ordinate/complex-zero collisions are retained. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem actualProfileParameters_bound (t : Fin 3 → ZeroOccurrence) :
    ∀ j, |actualProfileParameters t j| ≤ 1/2 := by
  intro j
  fin_cases j <;> exact (occurrence_displacement_lt _).le

theorem actualRationalKernel_integral (t : Fin 3 → ZeroOccurrence) :
    actualRationalKernel t = ∫ v : ℝ,
      profileIntegrand (actualProfileGap t 1) (actualProfileGap t 2)
        (actualProfileParameters t 0) (actualProfileParameters t 1) (actualProfileParameters t 2) v := by
  apply (integralProfile_eq _ _ _ _ _ _ _ _).symm <;>
    exact le_trans (occurrence_displacement_lt _).le (by norm_num)

theorem actualProfile_integrable (t : Fin 3 → ZeroOccurrence) :
    Integrable (profileIntegrand (actualProfileGap t 1) (actualProfileGap t 2)
      (actualProfileParameters t 0) (actualProfileParameters t 1) (actualProfileParameters t 2)) := by
  apply profileIntegrand_integrable <;>
    exact le_trans (actualProfileParameters_bound t _) (by norm_num)

theorem actualProfile_horizontal_bound (js : List (Fin 3)) (t : Fin 3 → ZeroOccurrence) :
    ‖horizontalPartial js (horizontalProfile (actualProfileGap t 1) (actualProfileGap t 2))
        (actualProfileParameters t)‖ ≤ profileDerivativeBound js.length :=
  horizontalPartial_bound js _ _ _ (actualProfileParameters_bound t)

theorem actualProfile_symmetric_second (t : Fin 3 → ZeroOccurrence) :
    ‖(actualRationalKernel t + horizontalProfile (actualProfileGap t 1) (actualProfileGap t 2)
        (-actualProfileParameters t))/2 - actualRealKernel t‖ ≤
      profileDerivativeBound 2 * horizontalSize (actualProfileParameters t)^2 / 2 := by
  simpa [actualRationalKernel, actualRealKernel, horizontalProfile, actualProfileGap, actualProfileParameters]
    using profile_symmetric_second_bound (actualProfileGap t 1) (actualProfileGap t 2)
      (actualProfileParameters t) (actualProfileParameters_bound t)

theorem actualProfile_symmetric_fourth (t : Fin 3 → ZeroOccurrence) :
    ‖(actualRationalKernel t + horizontalProfile (actualProfileGap t 1) (actualProfileGap t 2)
        (-actualProfileParameters t))/2 - actualRealKernel t -
      iteratedDeriv 2 (profileRay (actualProfileGap t 1) (actualProfileGap t 2) (actualProfileParameters t)) 0 / 2‖ ≤
      profileDerivativeBound 4 * horizontalSize (actualProfileParameters t)^4 / 24 := by
  simpa [actualRationalKernel, actualRealKernel, horizontalProfile, actualProfileGap, actualProfileParameters]
    using profile_symmetric_fourth_bound (actualProfileGap t 1) (actualProfileGap t 2)
      (actualProfileParameters t) (actualProfileParameters_bound t)

end
end HigherCorrelations
