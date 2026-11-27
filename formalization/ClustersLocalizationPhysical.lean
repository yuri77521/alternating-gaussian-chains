import ClustersLocalizationEnergy
import ClusterSeriesTrialMinimum
import ParticleDeficit

noncomputable section
namespace GaussianChains.Localization
open Real ClusterSeries Occupation

/-- Equation (3) for the actual particle energy on the full collision closure.
The Fourier tail is controlled by the published R(q) ≤ 2/3 hypothesis. -/
theorem physical_energy_semicircle_deficit {m : ℕ} {hN : 0 < 2*m}
    {s : ℝ} (hs : 0 < s) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    {x : Fin (2*m) → ℝ} (hx : Feasible hN 0 x) :
    (4-‖structureFactor x 1‖^2)/3 ≤
      ((2*m:ℕ):ℝ)*(imageEnergy s x-dipoleEnergy (2*m) s) /
        (2 * sqrt (π/s) * exp (-(π^2)/s)) := by
  rw [normalized_energy_deficit m (by omega) hs x]
  exact physical_semicircle_deficit hx (exp_pos _).le
    (exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hs)) hR

/-- The discrepancy of the best-aligned semicircle is at most 3F/2.
This estimate applies to every feasible cell before invoking minimality. -/
theorem first_mode_cost_le_deficit {m : ℕ} {hN : 0 < 2*m}
    {s : ℝ} (hs : 0 < s) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    {x : Fin (2*m) → ℝ} (hx : Feasible hN 0 x) :
    2-‖structureFactor x 1‖ ≤ 3/2 *
      (((2*m:ℕ):ℝ)*(imageEnergy s x-dipoleEnergy (2*m) s) /
        (2 * sqrt (π/s) * exp (-(π^2)/s))) := by
  have hf := physical_energy_semicircle_deficit hs hR hx
  have hprod := mul_nonneg (norm_nonneg (structureFactor x 1)) (sub_nonneg.mpr (structureFactor_one_le_two hx))
  nlinarith only [hf, hprod]

/-- Every globally minimizing feasible cell has small first-mode deficit
at the angular floor η = 2πh. This comparison does not assume odd clustering. -/
theorem groundState_first_mode_cost_le {m : ℕ} {hN : 0 < 2*m} {h s : ℝ}
    (hs : 0 < s) (h0 : 0 ≤ h) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    {x : Fin (2*m) → ℝ} (hx : IsGroundState hN h s x) :
    2-‖structureFactor x 1‖ ≤ 3*(m:ℝ)^2*(2*π*h)^2 := by
  have had : Feasible hN 0 x := fun i => h0.trans (hx.1 i)
  have hdef := physical_energy_semicircle_deficit hs hR had
  have ht := minimum_deficit_le m (by omega) hs hR h0 (floor_le_mean hx.1)
  dsimp only at ht
  rw [groundState_energy_eq_minimum hx] at hdef
  exact discrepancy_of_trial (norm_nonneg _) (structureFactor_one_le_two had) hdef ht

#print axioms physical_energy_semicircle_deficit
#print axioms groundState_first_mode_cost_le
end GaussianChains.Localization

