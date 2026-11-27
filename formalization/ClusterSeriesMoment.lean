import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace GaussianChains.ClusterSeries

/-- All polynomial moments of the positive Gaussian frequencies are finite. -/
theorem gaussianMoment_summable (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (d : ℕ) :
    Summable (fun n : ℕ => q ^ ((n + 1) ^ 2) * ((n + 1 : ℕ) : ℝ) ^ d) := by
  apply (summable_nat_add_iff (f := fun n : ℕ => q ^ (n ^ 2) * (n : ℝ)^d) 1).2
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_pow_mul_geometric_of_norm_lt_one d
      (show ‖q‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hq]))
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq.le hq1.le
    (show n ≤ n ^ 2 by simpa [sq] using Nat.le_mul_self n)) (by positivity)

/-- A per-mode Taylor estimate gives absolute convergence and the identical
moment bound after summation. The index `n` denotes frequency `n+1`. -/
theorem gaussian_tsum_remainder_bound {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (d : ℕ) (a : ℝ) (r : ℕ → ℝ)
    (hr : ∀ n, |r n| ≤ a * ((n + 1 : ℕ) : ℝ) ^ d) :
    Summable (fun n : ℕ => q ^ ((n + 1) ^ 2) * r n) ∧
    |∑' n : ℕ, q ^ ((n + 1) ^ 2) * r n| ≤
      a * ∑' n : ℕ, q ^ ((n + 1) ^ 2) * ((n + 1 : ℕ) : ℝ) ^ d := by
  have hmoment := gaussianMoment_summable q hq hq1 d
  have hterm (n : ℕ) : ‖q ^ ((n + 1) ^ 2) * r n‖ ≤
      a * (q ^ ((n + 1) ^ 2) * ((n + 1 : ℕ) : ℝ) ^ d) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq.le _),
      mul_left_comm a]
    exact mul_le_mul_of_nonneg_left (hr n) (pow_nonneg hq.le _)
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hmoment.mul_left a)
  refine ⟨hnorm.of_norm, ?_⟩
  rw [← Real.norm_eq_abs, ← hmoment.tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hterm (hmoment.mul_left a))

end GaussianChains.ClusterSeries
