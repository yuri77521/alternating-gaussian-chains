import ChainEnergy
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! The shifted theta transformation on a circle of unit period. -/
namespace GaussianChains

open Real

theorem cos_modes_hasSum {s : ℝ} (hs : 0 < s) (d : ℝ) :
    HasSum (fun n : ℕ => exp (-(π ^ 2) / s) ^ ((n + 1) ^ 2) *
      cos (2 * π * ((n + 1 : ℕ) : ℝ) * d))
      ((1 / 2 : ℝ) * (HurwitzZeta.cosKernel d (π / s) - 1)) := by
  apply ((HurwitzZeta.hasSum_nat_cosKernel₀ d (div_pos pi_pos hs)).mul_left
    (1 / 2 : ℝ)).congr_fun
  intro n
  rw [← exp_nat_mul]
  push_cast
  ring_nf

theorem summable_cos_modes {s : ℝ} (hs : 0 < s) (d : ℝ) :
    Summable (fun n : ℕ => exp (-(π ^ 2) / s) ^ ((n + 1) ^ 2) *
      cos (2 * π * ((n + 1 : ℕ) : ℝ) * d)) :=
  (cos_modes_hasSum hs d).summable

/-- No upper bound on the nome is required for this expansion. -/
theorem kernel_fourier {s : ℝ} (hs : 0 < s) (d : ℝ) :
    kernel s d =
    sqrt (π / s) * (1 + 2 * ∑' n : ℕ, exp (-(π ^ 2) / s) ^ ((n + 1) ^ 2) *
      cos (2 * π * ((n + 1 : ℕ) : ℝ) * d)) := by
  rw [kernel, (kernel_hasSum s d hs).tsum_eq, HurwitzZeta.evenKernel_functional_equation,
    (cos_modes_hasSum hs d).tsum_eq]
  have hInv : 1 / (s / π) = π / s := by rw [one_div_div]
  have hScale : 1 / (s / π) ^ (1 / 2 : ℝ) = sqrt (π / s) := by
    rw [← sqrt_eq_rpow, ← hInv, one_div, one_div, Real.sqrt_inv]
  rw [hInv, hScale]
  ring

/-- The Fourier series converges uniformly in the pair displacement at fixed width. -/
theorem continuous_kernel {s : ℝ} (hs : 0 < s) : Continuous (kernel s) := by
  let w := fun n : ℕ => exp (-(π ^ 2) / s) ^ ((n + 1) ^ 2)
  have hw : Summable w := by simpa [w] using summable_cos_modes hs 0
  have hc : Continuous (fun d : ℝ => ∑' n : ℕ, w n *
      cos (2 * π * ((n + 1 : ℕ) : ℝ) * d)) := by
    refine continuous_tsum (fun n => continuous_const.mul
      (continuous_cos.comp (continuous_const.mul continuous_id))) hw ?_
    intro n d
    have hn : 0 ≤ w n := pow_nonneg (exp_pos _).le _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs]
    exact mul_le_of_le_one_right hn (abs_cos_le_one _)
  change Continuous (fun d => kernel s d)
  simp_rw [kernel_fourier hs]
  exact continuous_const.mul (continuous_const.add (continuous_const.mul hc))

/-- The energy extends continuously to labelled cells with coincident sites. -/
theorem continuous_imageEnergy {N : ℕ} {s : ℝ} (hs : 0 < s) :
    Continuous (imageEnergy (N := N) s) := by
  unfold imageEnergy
  refine continuous_const.sub (continuous_const.mul (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => continuous_const.mul ?_))
  exact (continuous_kernel hs).comp ((continuous_apply j).sub (continuous_apply i))

end GaussianChains
