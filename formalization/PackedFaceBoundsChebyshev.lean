import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform bounds for the Chebyshev polynomials on the closed real unit interval. -/

namespace GaussianChains.PackedFace

open Polynomial Polynomial.Chebyshev

theorem abs_eval_T (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(T ℝ n).eval x| ≤ 1 := by
  obtain ⟨t, _, rfl⟩ := Real.surjOn_cos hx
  rw [T_real_cos]
  exact Real.abs_cos_le_one _

/-- Skipping two indices expresses each successive shell using a bounded first-kind
polynomial. This remains valid at both endpoints, without dividing by a sine. -/
private theorem U_two_step (k : ℤ) :
    U ℝ (k + 2) = 2 * T ℝ (k + 2) + U ℝ k := by
  have h := U_eq_X_mul_U_add_T ℝ (k + 1)
  rw [show k + 1 + 1 = k + 2 by ring] at h
  linear_combination 2 * h - U_add_two ℝ k

theorem abs_eval_U_pred (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(U ℝ ((n : ℤ) - 1)).eval x| ≤ (n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih _ =>
    have he : ((n + 2 : ℕ) : ℤ) - 1 = ((n : ℤ) - 1) + 2 := by omega
    rw [he, U_two_step, eval_add, eval_mul, eval_ofNat]
    calc
      _ ≤ |2 * (T ℝ (((n : ℤ) - 1) + 2)).eval x| + |(U ℝ ((n : ℤ) - 1)).eval x| :=
        abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        push_cast
        linarith [abs_eval_T (((n : ℤ) - 1) + 2) hx]

theorem abs_eval_derivative_T (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |((T ℝ n).derivative).eval x| ≤ (n : ℝ)^2 := by
  rw [T_derivative_eq_U, eval_mul, eval_intCast, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n), pow_two]
  exact mul_le_mul_of_nonneg_left (abs_eval_U_pred n hx) (Nat.cast_nonneg n)

theorem abs_eval_derivative_U_pred (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |((U ℝ ((n : ℤ) - 1)).derivative).eval x| ≤ (n : ℝ) * ((n : ℝ)-1)^2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih _ =>
    have he : ((n + 2 : ℕ) : ℤ) - 1 = ((n : ℤ) - 1) + 2 := by omega
    have hf : ((n : ℤ) - 1) + 2 = ((n + 1 : ℕ) : ℤ) := by omega
    rw [he, U_two_step, hf, derivative_add, derivative_mul, eval_add]
    simp only [derivative_ofNat, zero_mul, zero_add, eval_mul, eval_ofNat]
    calc
      _ ≤ |2 * ((T ℝ (n + 1 : ℕ)).derivative).eval x| +
          |((U ℝ ((n : ℤ) - 1)).derivative).eval x| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        have hT := abs_eval_derivative_T (n+1) hx
        push_cast at hT ⊢
        nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

theorem abs_eval_derivative_derivative_T (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |((T ℝ n).derivative.derivative).eval x| ≤ (n : ℝ)^4 := by
  rw [T_derivative_eq_U, derivative_intCast_mul, eval_mul, eval_intCast, Int.cast_natCast,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  cases n with
  | zero => simp
  | succ n =>
    calc
      _ ≤ ((n+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ)-1)^2) :=
        mul_le_mul_of_nonneg_left (abs_eval_derivative_U_pred (n+1) hx) (Nat.cast_nonneg _)
      _ ≤ _ := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ), pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3]

end GaussianChains.PackedFace
