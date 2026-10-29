import HigherCorrelations.TripleBoundaryMoments
import HigherCorrelations.TripleQuadrantGeometry
import Mathlib.MeasureTheory.Integral.Prod

/-! UNCONDITIONAL integrable boundary-layer majorants on the closed quadrant.
Both one-sided endpoints are included, and product measures are explicit. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_measure :
    (volume : Measure (ℝ × ℝ)).restrict tripleQuadrant =
      (volume.restrict (Ici (0:ℝ))).prod (volume.restrict (Ici (0:ℝ))) := by
  rw [Measure.prod_restrict,← Measure.volume_eq_prod]
  rfl

theorem tripleBoundary_moment_closed (n : ℕ) (a : ℝ) (ha : 0<a) :
    (∫ s : ℝ in Ici 0, s^n*Real.exp (-(a*s))) = (n.factorial:ℝ)/(a^(n+1)) := by
  rw [integral_Ici_eq_integral_Ioi]
  exact tripleBoundary_moment n a ha

theorem tripleBoundary_moment_closed_integrable (n : ℕ) (a : ℝ) (ha : 0<a) :
    IntegrableOn (fun s : ℝ => s^n*Real.exp (-(a*s))) (Ici 0) :=
  (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (tripleBoundary_moment_integrable n a ha)

theorem tripleBoundary_product_moment (m n : ℕ) (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫ p : ℝ × ℝ in tripleQuadrant,
      (p.1^m*Real.exp (-(a*p.1)))*(p.2^n*Real.exp (-(b*p.2)))) =
      ((m.factorial:ℝ)/a^(m+1))*((n.factorial:ℝ)/b^(n+1)) := by
  rw [tripleQuadrant_measure,integral_prod_mul
    (fun x : ℝ => x^m*Real.exp (-(a*x))) (fun y : ℝ => y^n*Real.exp (-(b*y))),
    tripleBoundary_moment_closed m a ha,tripleBoundary_moment_closed n b hb]

theorem tripleBoundary_product_moment_integrable (m n : ℕ) (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    IntegrableOn (fun p : ℝ × ℝ =>
      (p.1^m*Real.exp (-(a*p.1)))*(p.2^n*Real.exp (-(b*p.2)))) tripleQuadrant := by
  rw [IntegrableOn,tripleQuadrant_measure]
  exact (tripleBoundary_moment_closed_integrable m a ha).mul_prod
    (tripleBoundary_moment_closed_integrable n b hb)

theorem tripleBoundary_origin_mass_closed :
    (∫ p : ℝ × ℝ in tripleQuadrant, Real.exp (-(2*(p.1+p.2)))) = (1/4:ℝ) := by
  have he (p : ℝ × ℝ) : Real.exp (-(2*(p.1+p.2))) =
      (p.1^0*Real.exp (-(2*p.1)))*(p.2^0*Real.exp (-(2*p.2))) := by
    simp only [pow_zero,one_mul,← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [tripleBoundary_product_moment 0 0 2 2 (by norm_num) (by norm_num)]
  norm_num

theorem tripleBoundary_origin_first_moment :
    (∫ p : ℝ × ℝ in tripleQuadrant,
      (p.1+p.2)*Real.exp (-(2*(p.1+p.2)))) = (1/4:ℝ) := by
  have he (p : ℝ × ℝ) : (p.1+p.2)*Real.exp (-(2*(p.1+p.2))) =
      (p.1^1*Real.exp (-(2*p.1)))*(p.2^0*Real.exp (-(2*p.2))) +
      (p.1^0*Real.exp (-(2*p.1)))*(p.2^1*Real.exp (-(2*p.2))) := by
    rw [show -(2*(p.1+p.2)) = -(2*p.1)+ -(2*p.2) by ring,Real.exp_add]
    ring
  simp_rw [he]
  rw [integral_add
    (tripleBoundary_product_moment_integrable 1 0 2 2 (by norm_num) (by norm_num))
    (tripleBoundary_product_moment_integrable 0 1 2 2 (by norm_num) (by norm_num)),
    tripleBoundary_product_moment 1 0 2 2 (by norm_num) (by norm_num),
    tripleBoundary_product_moment 0 1 2 2 (by norm_num) (by norm_num)]
  norm_num

end
end HigherCorrelations
