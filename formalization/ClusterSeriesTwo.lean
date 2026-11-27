import ClustersTwo
import ClusterSeriesCandidate

namespace GaussianChains.ClusterSeries

open Real

/-- The global energy part of Corollary 2 for two particles: all positive
Fourier modes of the opposite singleton blocks reduce to the collision
dipole energy at every feasible floor. -/
theorem minimumEnergy_two_eq_dipole {s h : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (h₀ : 0 ≤ h) (h₁ : h ≤ 1/2) :
    minimumEnergy (by decide : 0 < 2) h s = dipoleEnergy 2 s := by
  obtain ⟨hpair, hclass⟩ := two_site_classification hs hR h₀ h₁
  have hground : IsGroundState (by decide) h s antipodalPair := by
    exact ⟨hpair, (hclass _ hpair).mpr ⟨0, by simp⟩⟩
  rw [← groundState_energy_eq_minimum hground, two_imageEnergy_eq hs, dipoleEnergy]
  norm_num [antipodalPair]
  ring

/-- Fourier form of that same attained global minimum. -/
theorem minimumEnergy_two_fourier {s h : ℝ} (hs : 0 < s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (h₀ : 0 ≤ h) (h₁ : h ≤ 1/2) :
    minimumEnergy (by decide : 0 < 2) h s =
      1 - 4*sqrt (π/s) * parityMoment Odd (exp (-(π^2)/s)) 0 := by
  rw [minimumEnergy_two_eq_dipole hs hR h₀ h₁, dipoleEnergy, kernel_dipole_difference hs]
  push_cast
  ring

#print axioms minimumEnergy_two_fourier

end GaussianChains.ClusterSeries

