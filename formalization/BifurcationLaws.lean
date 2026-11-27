import BifurcationCritical
import BifurcationPitch

/-! The laws at the certified width-eight threshold, in physical energy units. -/
noncomputable section
namespace GaussianChains.Bifurcation
open Filter Asymptotics Set
open scoped Topology

/-- Equation (11) specialized to the proved signs of the actual critical
derivatives. The negative branch is obtained by reflection in t. -/
theorem widthEight_pitch_laws :
    ∃ t : ℝ → ℝ, Tendsto t (𝓝[>] 0) (𝓝 0) ∧
      (∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ deriv (faceEnergy (hcEight+δ)) (t δ) = 0) ∧
      ((fun δ => t δ - Real.sqrt (-6*mixedCritical/fourthCritical)*δ^(1/2:ℝ))
        =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
      ((fun δ => faceEnergy (hcEight+δ) 0 - faceEnergy (hcEight+δ) (t δ) -
        (3*mixedCritical^2/(2*fourthCritical))*δ^2)
        =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) ∧
      ∃ r > (0:ℝ), ∀ᶠ δ in 𝓝[>] 0, ∀ u ∈ Ioc 0 r,
        deriv (faceEnergy (hcEight+δ)) u = 0 ↔ u = t δ := by
  have hA : mixedCritical < 0 := lt_trans critical_coefficients.1.2 (by norm_num)
  have hB : 0 < fourthCritical := lt_trans (by norm_num) critical_coefficients.2.1.1
  apply packedEnergy8_bifurcation hA hB critical_zero _ rfl
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] <;> rfl

end GaussianChains.Bifurcation
