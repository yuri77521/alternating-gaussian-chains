import ClusterSeriesDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace GaussianChains.ClusterSeries

/-- The difference of two adjacent cosines is small to second order, uniformly
in the angular step. This estimate preserves the sharp coefficient. -/
theorem adjacent_cos_bound (r w : ℝ) (hr : 0 ≤ r) :
    2 * |Real.cos (r*w) - Real.cos ((r+1)*w)| ≤ (2*r+1)*w^2 := by
  let x := r*w
  let y := (r+1)*w
  change 2 * |Real.cos x - Real.cos y| ≤ _
  rw [Real.cos_sub_cos, abs_mul, abs_mul]
  rw [show |(-2:ℝ)| = 2 by norm_num]
  calc
    _ ≤ 2 * (2 * |(x+y)/2| * |(x-y)/2|) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num))
          Real.abs_sin_le_abs (abs_nonneg _) (by positivity)) (by norm_num)
    _ = |x+y| * |x-y| := by rw [abs_div, abs_div]; norm_num; ring
    _ = (2*r+1)*w^2 := by
      rw [show x+y = (2*r+1)*w by dsimp [x,y]; ring,
        show x-y = -w by dsimp [x,y]; ring,
        abs_mul, abs_of_nonneg (show 0 ≤ 2*r+1 by linarith), abs_neg]
      rw [mul_assoc, ← sq, sq_abs]

/-- Sharp quadratic bound for every packed odd block. -/
theorem block_deficit_le (j : ℕ) (w : ℝ) :
    |1 - block j w| ≤ coeff j * w^2 / 2 := by
  induction j using Nat.twoStepInduction with
  | zero => simp [block, coeff]
  | one =>
    have h := adjacent_cos_bound 0 w le_rfl
    simp only [zero_mul, Real.cos_zero, zero_add, one_mul] at h
    have hu : 1 - block 1 w = 2 * (1 - Real.cos w) := by
      simp [block]; ring
    rw [hu, abs_mul]
    norm_num [coeff] at h ⊢
    linarith only [h]
  | more j ih _ =>
    let r : ℝ := (j:ℝ)+1
    have h := adjacent_cos_bound r w (by dsimp [r]; positivity)
    have step : 1 - block (j+2) w = (1-block j w) +
        2*(Real.cos (r*w)-Real.cos ((r+1)*w)) := by
      simp only [block, Nat.cast_succ, r]; ring
    rw [step]
    calc
      _ ≤ |1-block j w| + |2*(Real.cos (r*w)-Real.cos ((r+1)*w))| := abs_add_le ..
      _ ≤ coeff j*w^2/2 + (2*r+1)*w^2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add ih h
      _ = _ := by simp [r, coeff]; ring

/-- Odd modes of the trial can lose at most the stated quadratic mass. -/
theorem trial_odd_deficit_le (k l : ℕ) (w : ℝ) :
    4 - (block k w + block l w)^2 ≤ 2*(coeff k + coeff l)*w^2 := by
  have hk := (le_abs_self _).trans (block_deficit_le k w)
  have hl := (le_abs_self _).trans (block_deficit_le l w)
  nlinarith [sq_nonneg (2 - (block k w + block l w))]

/-- Even modes start with zero dipole mass and can only decrease the deficit. -/
theorem trial_even_deficit_le (k l : ℕ) (w : ℝ) :
    0 - (block k w - block l w)^2 ≤ 0 := by linarith [sq_nonneg (block k w - block l w)]

end GaussianChains.ClusterSeries

