import HigherCorrelations.ProfileMicroscopicBounds
import HigherCorrelations.TripleBoundaryLocalLimits

/-! UNCONDITIONAL microscopic limit uniform in gaps and horizontal parameters.
R is fixed; all five parameters may vary within the closed box. No zero sum
is interchanged with this limit and no critical-line substitution is made. -/
namespace HigherCorrelations
noncomputable section
open Filter Set
open scoped Topology

theorem microscopic_meanSpacing_ge_one (T : ℝ) (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) :
    1≤ meanSpacing T := by
  have hp : 0<2*Real.pi := by positivity
  have hb : Real.exp (2*Real.pi)≤T/(2*Real.pi) := (le_div_iff₀ hp).mpr (by nlinarith [hT])
  have hh := Real.log_le_log (Real.exp_pos _) hb
  rw [Real.log_exp] at hh
  exact (le_div_iff₀ hp).mpr (by simpa only [one_mul] using hh)

theorem microscopic_meanSpacing_tendsto : Tendsto meanSpacing atTop atTop := by
  have hp : 0<2*Real.pi := by positivity
  exact (Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hp)).atTop_div_const hp

theorem rationalProfile_microscopic_bound (R T u v e f g : ℝ) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (hu : |u|≤R) (hv : |v|≤R)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/meanSpacing T) (v/meanSpacing T) e f g-rationalProfile 0 0 e f g‖ ≤
      (16*Real.pi*R*(R+1)/9)/meanSpacing T :=
  rationalProfile_scaled_gap_bound R (meanSpacing T) u v e f g hR
    (microscopic_meanSpacing_ge_one T hT) hu hv he hf hg

theorem rationalProfile_microscopic_tendstoUniformlyOn (R : ℝ) (hR : 0≤R) :
    TendstoUniformlyOn
      (fun T (p : Fin 5 → ℝ) => rationalProfile (p 0/meanSpacing T) (p 1/meanSpacing T) (p 2) (p 3) (p 4))
      (fun p => rationalProfile 0 0 (p 2) (p 3) (p 4)) atTop (profileMicroscopicBox R) := by
  have hlim : Tendsto (fun T => (16*Real.pi*R*(R+1)/9)/meanSpacing T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop microscopic_meanSpacing_tendsto
  apply tripleBoundary_uniform_of_envelope _ _ _ _ hlim
  filter_upwards [eventually_ge_atTop (2*Real.pi*Real.exp (2*Real.pi))] with T hT
  intro p hp
  exact rationalProfile_microscopic_bound R T (p 0) (p 1) (p 2) (p 3) (p 4) hR hT
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2

theorem rationalProfile_microscopic_zero_gaps (ℓ e f g : ℝ) :
    rationalProfile (0/ℓ) (0/ℓ) e f g=rationalProfile 0 0 e f g := by simp

theorem rationalProfile_microscopic_zero_radius (ℓ u v e f g : ℝ)
    (hu : |u|≤0) (hv : |v|≤0) :
    rationalProfile (u/ℓ) (v/ℓ) e f g=rationalProfile 0 0 e f g := by
  have hu0 : u=0 := by have h := abs_le.mp hu; linarith
  have hv0 : v=0 := by have h := abs_le.mp hv; linarith
  simp [hu0,hv0]

theorem rationalProfile_microscopic_coincident_gaps (R ℓ u e f g : ℝ) (hR : 0≤R)
    (hℓ : 1≤ℓ) (hu : |u|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/ℓ) (u/ℓ) e f g-rationalProfile 0 0 e f g‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ :=
  rationalProfile_scaled_gap_bound R ℓ u u e f g hR hℓ hu hu he hf hg

theorem rationalProfile_microscopic_closed_endpoints (R ℓ u v : ℝ) (hR : 0≤R)
    (hℓ : 1≤ℓ) (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/ℓ) (v/ℓ) (1/2) (-1/2) (1/2)-rationalProfile 0 0 (1/2) (-1/2) (1/2)‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ :=
  rationalProfile_scaled_gap_bound R ℓ u v (1/2) (-1/2) (1/2) hR hℓ hu hv
    (by norm_num) (by norm_num) (by norm_num)

end
end HigherCorrelations
