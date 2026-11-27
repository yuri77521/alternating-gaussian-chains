import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Normal convergence of the endpoint series (10) on a complex neighborhood
of both real endpoint curves. The majorant works simultaneously for all three
arguments in the indicated polydisc. -/

namespace GaussianChains.PackedFace

open Polynomial Polynomial.Chebyshev Set Filter
noncomputable section

private theorem complex_two_step_bound (f : ℕ → ℂ) (x : ℂ) (hx : ‖x‖ ≤ 2)
    (h0 : ‖f 0‖ ≤ 1) (h1 : ‖f 1‖ ≤ 5)
    (hs : ∀ n, f (n+2) = 2*x*f (n+1)-f n) (n : ℕ) :
    ‖f n‖ ≤ (5:ℝ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => simpa using h1
  | more n h h' =>
    rw [hs]
    calc
      _ ≤ ‖2*x*f (n+1)‖ + ‖f n‖ := norm_sub_le _ _
      _ ≤ (2*2)*(5:ℝ)^(n+1) + 5^n := by
        rw [norm_mul, norm_mul, Complex.norm_two]
        gcongr
      _ ≤ (5:ℝ)^(n+2) := by
        simp only [pow_succ]
        linarith [show (0:ℝ) ≤ 5^n by positivity]

theorem norm_eval_T_complex (n : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 2) :
    ‖(T ℂ n).eval x‖ ≤ (5:ℝ)^n := by
  refine complex_two_step_bound (fun n : ℕ => (T ℂ n).eval x) x hx (by simp) (by simpa using hx.trans (by norm_num : (2:ℝ) ≤ 5)) ?_ n
  intro k
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, T_add_two, eval_sub, eval_mul,
    eval_X, eval_ofNat]

theorem norm_eval_U_complex (n : ℕ) {x : ℂ} (hx : ‖x‖ ≤ 2) :
    ‖(U ℂ n).eval x‖ ≤ (5:ℝ)^n := by
  refine complex_two_step_bound (fun n : ℕ => (U ℂ n).eval x) x hx (by simp) ?_ ?_ n
  · simp only [Nat.cast_one, U_one, eval_mul, eval_ofNat, eval_X, norm_mul, Complex.norm_two]
    linarith
  · intro k
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, U_add_two, eval_sub, eval_mul,
      eval_X, eval_ofNat]

def complexSlopeMode (n : ℕ) (q x z : ℂ) : ℂ :=
  (-1:ℂ)^(n+1) * n * q^(n^2-1) * (2*(T ℂ n).eval x-1)^2 * (U ℂ ((n:ℤ)-1)).eval z

/-- We only need a neighborhood of the real arcs, where |q| ≤ .34 and |x|,|z| ≤ 1. -/
def slopeMajorant (n : ℕ) : ℝ := (n:ℝ) * (1/2:ℝ)^(n^2-1) * (3 * 5^n)^2 * 5^n

theorem norm_complexSlopeMode_le (n : ℕ) {q x z : ℂ}
    (hq : ‖q‖ ≤ 1/2) (hx : ‖x‖ ≤ 2) (hz : ‖z‖ ≤ 2) :
    ‖complexSlopeMode n q x z‖ ≤ slopeMajorant n := by
  have ht : ‖2*(T ℂ n).eval x-1‖ ≤ 3*(5:ℝ)^n := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul, norm_one, Complex.norm_two]
    linarith [norm_eval_T_complex n hx, one_le_pow₀ (by norm_num : (1:ℝ) ≤ 5) (n := n)]
  have hu : ‖(U ℂ ((n:ℤ)-1)).eval z‖ ≤ (5:ℝ)^n := by
    cases n with
    | zero => simp
    | succ k =>
      simp only [Nat.cast_succ, add_sub_cancel_right]
      exact (norm_eval_U_complex k hz).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  simp only [complexSlopeMode, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, slopeMajorant]
  gcongr

/-- On the tail, the three Chebyshev factors cost at most `125^n`. Even
after absorbing the factor `n` into `2^n`, the Gaussian leaves a summable
geometric factor for every mode from ten on. -/
theorem summable_slopeMajorant : Summable slopeMajorant := by
  apply Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => 9 * (1/2:ℝ)^n)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 9)
  filter_upwards [eventually_ge_atTop 10] with n hn
  have hn2 : (n:ℝ) ≤ (2:ℝ)^n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h125 : (125:ℝ)^n ≤ (128:ℝ)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hexp : 8*n+n ≤ n^2-1 := by
    have hnn : 10*n ≤ n*n := Nat.mul_le_mul_right _ hn
    rw [pow_two]
    omega
  have hg := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) hexp
  have ha : slopeMajorant n = 9 * (((n:ℝ) * 125^n) * (1/2:ℝ)^(n^2-1)) := by
    unfold slopeMajorant
    rw [show (125:ℝ)^n = ((5:ℝ)^n)^3 by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ slopeMajorant n by unfold slopeMajorant; positivity), ha]
  gcongr 9 * ?_
  calc
    _ ≤ ((2:ℝ)^n * 128^n) * (1/2:ℝ)^(8*n+n) := by gcongr
    _ = _ := by
      rw [← mul_pow, pow_add, pow_mul, ← mul_assoc, ← mul_pow,
        show ((2:ℝ)*128) * (1/2)^8 = 1 by norm_num, one_pow, one_mul]

end
end GaussianChains.PackedFace
