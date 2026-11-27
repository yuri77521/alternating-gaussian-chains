import ClusterSeriesDefs
import ClusterSeriesCosine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace GaussianChains.ClusterSeries

theorem block_abs_le (k : ℕ) (w : ℝ) : |block k w| ≤ 2 * (k : ℝ) + 1 := by
  induction k with
  | zero => simp [block]
  | succ k ih =>
    calc
      |block (k + 1) w| ≤ |2 * Real.cos (((k : ℝ) + 1) * w)| + |block k w| :=
        abs_sub _ _
      _ ≤ 2 * 1 + (2 * (k : ℝ) + 1) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (mul_le_mul_of_nonneg_left (abs_le.mpr
          ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (by norm_num)) ih
      _ = _ := by push_cast; ring

/-- The constant may depend on the number of sites but works for every angular
step, including the high modes of the Fourier sum. -/
theorem block_fourth_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, |block k w - blockPoly k w| ≤ C * w^6 := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro w
    simp [block, blockPoly, coeff]
  | succ k ih =>
    obtain ⟨C, hC, hc⟩ := ih
    let r : ℝ := k + 1
    refine ⟨2 / 720 * r^6 + C, by positivity, ?_⟩
    intro w
    have step : block (k+1) w - blockPoly (k+1) w =
        2 * (Real.cos (r*w) - (1 - (r*w)^2/2 + (r*w)^4/24)) -
          (block k w - blockPoly k w) := by
      simp only [block, blockPoly, coeff, Nat.cast_succ, r]
      ring
    rw [step]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * ((1/720 : ℝ) * (r*w)^6) + C*w^6 :=
        add_le_add (mul_le_mul_of_nonneg_left (cos_fourth_bound _) (by norm_num)) (hc _)
      _ = _ := by ring

end GaussianChains.ClusterSeries

