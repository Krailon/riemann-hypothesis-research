import HigherCorrelations.ConstantKernelDefinitions
namespace HigherCorrelations
noncomputable section

theorem constantKernelEmpty_profile (a d : ℝ) (δ : Fin 3 → ℝ) :
    constantKernelEmpty a d δ = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      rationalProfile a d (if e 1 then -δ 1 else δ 1)
        (if e 2 then -δ 2 else δ 2) (if e 0 then -δ 0 else δ 0) := by sorry

theorem constantKernelEmpty_symmetric (a d : ℝ) (δ : Fin 3 → ℝ) :
    constantKernelEmpty a d δ = (1/8:ℂ)*∑ e : Fin 3 → Bool,
      (horizontalProfile a d (constantKernelParameters δ e)+
        horizontalProfile a d (-constantKernelParameters δ e))/2 := by sorry

theorem constantKernelEmpty_horizontal_bound (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a d δ-rationalProfile a d 0 0 0‖ ≤
      3072*Real.pi*(∑ j, δ j^2) := by sorry

theorem constantKernelEmpty_global_bound (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) : ‖constantKernelEmpty a d δ‖ ≤ 7*Real.pi/9 := by sorry

theorem constantKernel_real_gap_bound (a d : ℝ) (hg : a^2+d^2 ≤ 1) :
    ‖rationalProfile a d 0 0 0-kernelBenchmark‖ ≤ 4*Real.pi*(a^2+d^2) := by sorry

theorem constantKernelEmpty_pointwise (a d : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a d δ-kernelBenchmark‖ ≤
      constantKernelBound*min (constantKernelEnergy a d δ) 1 := by sorry

theorem constantKernelEmpty_origin : constantKernelEmpty 0 0 0 = kernelBenchmark := by sorry

theorem constantKernelEmpty_coincident (a : ℝ) (δ : Fin 3 → ℝ)
    (hδ : ∀ j, |δ j| ≤ 1/2) :
    ‖constantKernelEmpty a a δ-kernelBenchmark‖ ≤
      constantKernelBound*min (2*a^2+∑ j, δ j^2) 1 := by sorry

theorem constantKernelEmpty_cube_endpoints (a d : ℝ) (e : Fin 3 → Bool) :
    ‖constantKernelEmpty a d (fun j => if e j then -(1/2) else 1/2)-kernelBenchmark‖ ≤
      constantKernelBound*min (a^2+d^2+3/4) 1 := by sorry

end
end HigherCorrelations
