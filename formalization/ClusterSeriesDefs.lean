import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace GaussianChains.ClusterSeries

/-- Fourier amplitude of a centered, packed block of (2k+1) alternating sites.
Adding a site at each end flips the charges of the old block. -/
noncomputable def block : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, w => 2 * Real.cos (((k : ℝ) + 1) * w) - block k w

/-- Signed second moment of the unit-step block. -/
noncomputable def coeff (k : ℕ) : ℝ := (k : ℝ) * (k + 1)

/-- The block's even Taylor polynomial through degree four in the angular step. -/
noncomputable def blockPoly (k : ℕ) (w : ℝ) : ℝ :=
  1 - coeff k * w^2 / 2 + coeff k * (coeff k - 1) * w^4 / 24

/-- Positive-frequency Fourier mass of packed antipodal blocks. The physical
gap fraction is `h`; the input `η` is its angular value `2πh`. -/
noncomputable def packedMass (k l : ℕ) (q η : ℝ) : ℝ :=
  ∑' n : ℕ, q ^ ((n+1)^2) *
    (block k (((n+1:ℕ):ℝ)*η) - (-1:ℝ)^(n+1) * block l (((n+1:ℕ):ℝ)*η))^2

end GaussianChains.ClusterSeries

