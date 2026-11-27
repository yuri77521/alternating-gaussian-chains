import ChainFourier
import ChainGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! A one-dimensional representation of the aligned semicircle deficit.
On an occupied (even-index) gap the cost integrates the negative part of
sine; on the complementary gaps it integrates the positive part. -/
noncomputable section
namespace GaussianChains.JumpLocalization
open Real MeasureTheory Finset Set

def jumpSign (k : ℕ) : ℝ := if k % 2 = 0 then -1 else 1
def density (k : ℕ) (u : ℝ) : ℝ := max (jumpSign k * sin u) 0
def gapCost (θ : ℕ → ℝ) (k : ℕ) : ℝ := ∫ u in θ k..θ (k+1), density k u

theorem density_nonneg (k : ℕ) (u : ℝ) : 0 ≤ density k u := le_max_right _ _

theorem density_continuous (k : ℕ) : Continuous (density k) :=
  (continuous_const.mul continuous_sin).max continuous_const

private theorem pos_integral (t : ℝ) : (∫ u in t..t+2*π, max (sin u) 0) = 2 := by
  have hp : Function.Periodic (fun u => max (sin u) 0) (2*π) := fun u => by
    simp only [sin_add_two_pi]
  rw [hp.intervalIntegral_add_eq t 0, zero_add]
  have hc : Continuous (fun u => max (sin u) 0) := continuous_sin.max continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 π)
    (hc.intervalIntegrable π (2*π))]
  have h₁ : (∫ u in 0..π, max (sin u) 0) = ∫ u in 0..π, sin u := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact max_eq_left (sin_nonneg_of_mem_Icc (uIcc_of_le pi_pos.le ▸ hu))
  have h₂ : (∫ u in π..2*π, max (sin u) 0) = ∫ _u in π..2*π, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith [pi_pos] : π ≤ 2*π)] at hu
    have h := sin_nonneg_of_nonneg_of_le_pi (x := u-π) (by linarith [hu.1]) (by linarith [hu.2])
    rw [sin_sub_pi] at h
    exact max_eq_right (by linarith)
  rw [h₁, h₂, integral_sin]
  norm_num

private theorem cost_eq (θ : ℕ → ℝ) (k : ℕ) :
    gapCost θ k = (∫ u in θ k..θ (k+1), max (sin u) 0) -
      if k % 2 = 0 then cos (θ k) - cos (θ (k+1)) else 0 := by
  by_cases he : k % 2 = 0
  · have hd (u : ℝ) : density k u = max (sin u) 0 - sin u := by
      unfold density jumpSign
      rw [if_pos he, neg_one_mul]
      by_cases h : 0 ≤ sin u
      · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      · simp [max_eq_right (not_le.mp h).le, max_eq_left (neg_nonneg.mpr (not_le.mp h).le)]
    simp_rw [gapCost, hd, if_pos he]
    rw [intervalIntegral.integral_sub ((continuous_sin.max continuous_const).intervalIntegrable _ _)
      (continuous_sin.intervalIntegrable _ _), integral_sin]
  · simp [gapCost, density, jumpSign, he]

private theorem even_gaps_cos (θ : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (2*m), if k % 2 = 0 then cos (θ k) - cos (θ (k+1)) else 0) =
      ∑ k ∈ range (2*m), (-1:ℝ)^k * cos (θ k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, ih]
    simp [pow_add, pow_mul, Nat.add_mod]
    <;> ring

/-- Any even number of alternating gaps in one full turn. -/
theorem sum_gapCost (θ : ℕ → ℝ) (m : ℕ) (hθ : θ (2*m) = θ 0 + 2*π) :
    ∑ k ∈ range (2*m), gapCost θ k = 2 - ∑ k ∈ range (2*m), (-1:ℝ)^k * cos (θ k) := by
  simp_rw [cost_eq]
  rw [Finset.sum_sub_distrib, even_gaps_cos, intervalIntegral.sum_integral_adjacent_intervals
    (fun _ _ => (continuous_sin.max continuous_const).intervalIntegrable _ _), hθ, pos_integral]

def siteAngle {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (n : ℕ) : ℝ :=
  2*π*liftSite hN x n

theorem siteAngle_period {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (n : ℕ) :
    siteAngle hN x (n+N) = siteAngle hN x n + 2*π := by
  rw [siteAngle, liftSite_add_period]
  unfold siteAngle
  ring

theorem sum_gapCost_eq_deficit {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) :
    ∑ k ∈ range (2*m), gapCost (siteAngle hN x) k = 2 - (structureFactor x 1).re := by
  have hp := siteAngle_period hN x 0
  rw [Nat.zero_add] at hp
  rw [sum_gapCost _ _ hp, structureFactor, Complex.re_sum, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply sum_congr rfl
  intro i _
  simp only [siteAngle, liftSite_fin, Nat.cast_one, mul_one, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, charge]

theorem siteAngle_gap_floor {N : ℕ} {hN : 0 < N} {x : Fin N → ℝ} {h : ℝ}
    (hx : Feasible hN h x) (n : ℕ) :
    2*π*h ≤ siteAngle hN x (n+1) - siteAngle hN x n := by
  have hg := hx ⟨n%N, Nat.mod_lt _ hN⟩
  rw [← gap_lift_period] at hg
  unfold siteAngle
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left hg (by positivity)

end GaussianChains.JumpLocalization
