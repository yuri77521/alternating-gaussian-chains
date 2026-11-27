import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
namespace GaussianChains.Localization
open Real

/-- Between the good central cuts of the occupied and unoccupied semicircles,
only the odd endpoint π is close enough. In the other half it is 2π.
The input angle is lifted to one turn starting at the occupied cut. -/
theorem endpoint_of_arc {y z θ ρ : ℝ}
    (hy₀ : π/4 ≤ y) (hy₁ : y ≤ 3*π/4)
    (hz₀ : 5*π/4 ≤ z) (hz₁ : z ≤ 7*π/4)
    (hθ₀ : y ≤ θ) (hθ₁ : θ ≤ y+2*π) (hr : ρ < π/4)
    (hloc : ∃ k : ℤ, |θ - (k:ℝ)*π| ≤ ρ) :
    (θ ≤ z → |θ-π| ≤ ρ) ∧ (z ≤ θ → |θ-2*π| ≤ ρ) := by
  obtain ⟨k, hk⟩ := hloc
  have hh := abs_le.mp hk
  constructor
  · intro h
    have hkl : 0 < k := by
      by_contra! he
      have hc : (k:ℝ) ≤ 0 := by exact_mod_cast he
      linarith only [hh.2, hr, hθ₀, hy₀, mul_nonpos_of_nonpos_of_nonneg hc pi_pos.le]
    have hku : k < 2 := by
      by_contra! he
      have hc : (2:ℝ) ≤ k := by exact_mod_cast he
      linarith only [hh.1, hr, h, hz₁, mul_le_mul_of_nonneg_right hc pi_pos.le]
    have he : k = 1 := by omega
    simpa [he] using hk
  · intro h
    have hkl : 1 < k := by
      by_contra! he
      have hc : (k:ℝ) ≤ 1 := by exact_mod_cast he
      linarith only [hh.2, hr, h, hz₀, mul_le_mul_of_nonneg_right hc pi_pos.le]
    have hku : k < 3 := by
      by_contra! he
      have hc : (3:ℝ) ≤ k := by exact_mod_cast he
      linarith only [hh.1, hr, hθ₁, hy₁, mul_le_mul_of_nonneg_right hc pi_pos.le]
    have he : k = 2 := by omega
    simpa [he] using hk

/-- Integer-period shifts in a change of cut preserve the absolute localization
radius, including for a site whose gap crosses the displayed origin. -/
theorem shift_period_endpoint {θ ρ : ℝ} (h : ∃ k : ℤ, |θ-(k:ℝ)*π| ≤ ρ) (l : ℤ) :
    ∃ k : ℤ, |θ + (l:ℝ)*(2*π) - (k:ℝ)*π| ≤ ρ := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k+2*l,?_⟩
  rw [show θ+(l:ℝ)*(2*π)-((k+2*l:ℤ):ℝ)*π = θ-(k:ℝ)*π by push_cast; ring]
  exact hk

/-- The published small-floor restriction separates the two neighborhoods
strictly from both middle cuts. -/
theorem localization_radius_lt_quarter {N C η : ℝ} (hN : 2 ≤ N) (hC : 1 ≤ C)
    (hη : 0 ≤ η) (hsmall : η ≤ 1/(N*C^2)) : C*η < π/4 := by
  have hp : 0 < N*C^2 := by positivity
  have h := (le_div_iff₀ hp).1 hsmall
  have hf : 2 ≤ N*C := by
    calc 2 = 2*1 := by ring
         _ ≤ N*C := mul_le_mul hN hC (by norm_num) (by linarith)
  have hh := mul_le_mul_of_nonneg_left hf (mul_nonneg (by linarith : 0 ≤ C) hη)
  nlinarith only [h,hh,pi_gt_three]

end GaussianChains.Localization

