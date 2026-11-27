import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The summand of the endpoint slope (10), and its derivatives before
the higher modes are estimated. The same expressions work for the central
endpoint and for the outer contact where the abscissa also varies. -/
noncomputable section

namespace GaussianChains.PackedFace
open Polynomial.Chebyshev

def modeT (n : ℕ) (x : ℝ) : ℝ := (T ℝ n).eval x
def modeU (n : ℕ) (z : ℝ) : ℝ := (U ℝ ((n : ℤ)-1)).eval z

def endpointMode (n : ℕ) (q x z : ℝ) : ℝ :=
  (-1:ℝ)^(n+1) * n * q^(n^2-1) * (2*modeT n x-1)^2 * modeU n z

def endpointSlope (q x z : ℝ) : ℝ := ∑' k : ℕ, endpointMode (k+1) q x z

def endpointDx (n : ℕ) (q x z dz : ℝ) : ℝ :=
  (-1:ℝ)^(n+1) * n * q^(n^2-1) *
    (4*(2*modeT n x-1)*(T ℝ n).derivative.eval x*modeU n z +
      (2*modeT n x-1)^2 * (U ℝ ((n:ℤ)-1)).derivative.eval z * dz)

def endpointDq (n : ℕ) (q x z : ℝ) : ℝ :=
  (-1:ℝ)^(n+1) * n * ((n^2-1 : ℕ) : ℝ) * q^((n^2-1)-1) *
    (2*modeT n x-1)^2 * modeU n z

theorem endpointMode_hasDerivAt_x (n : ℕ) (q x dz : ℝ) {z : ℝ → ℝ}
    (hz : HasDerivAt z dz x) :
    HasDerivAt (fun u => endpointMode n q u (z u)) (endpointDx n q x (z x) dz) x := by
  have ht := (T ℝ n).hasDerivAt x
  have hu : HasDerivAt (fun t => modeU n (z t)) ((U ℝ ((n : ℤ)-1)).derivative.eval (z x) * dz) x :=
    ((U ℝ ((n : ℤ)-1)).hasDerivAt (z x)).comp x hz
  have ha := (((ht.const_mul 2).sub_const 1).pow 2)
  convert ((ha.fun_mul hu).const_mul ((-1:ℝ)^(n+1)*n*q^(n^2-1))) using 1 <;>
    first | (funext t; dsimp [endpointMode, modeT, modeU]; ring) |
      (dsimp [endpointDx, modeT, modeU]; ring)

theorem endpointMode_hasDerivAt_q (n : ℕ) (q x z : ℝ) :
    HasDerivAt (fun u => endpointMode n u x z) (endpointDq n q x z) q := by
  have hw := hasDerivAt_pow (n^2-1) q
  have hd := (((hw.const_mul ((-1:ℝ)^(n+1)*n)).mul_const ((2*modeT n x-1)^2)).mul_const (modeU n z))
  convert hd using 1 <;> dsimp [endpointDq, endpointMode] <;> ring

theorem endpointMode_scaled_q {n : ℕ} (hn : 2 ≤ n) (q x z : ℝ) :
    q * endpointDq n q x z = ((n^2-1 : ℕ) : ℝ) * endpointMode n q x z := by
  have h : n^2-1 = (n^2-1-1)+1 := by have := Nat.pow_le_pow_left hn 2; omega
  have hw : q^(n^2-1-1) * q = q^(n^2-1) := by
    rw [← pow_succ, ← h]
  simp only [endpointDq, endpointMode]
  linear_combination (-1:ℝ)^(n+1) * n * ((n^2-1 : ℕ) : ℝ) *
    (2*modeT n x-1)^2 * modeU n z * hw

/-- The first two actual summands are the polynomial low modes used in the
endpoint derivative tests. -/
theorem endpointMode_one_two (q x z : ℝ) :
    endpointMode 1 q x z + endpointMode 2 q x z =
      (2*x-1)^2-4*q^3*(4*x^2-3)^2*z := by
  norm_num [endpointMode, modeT, modeU, T_two]
  ring

end GaussianChains.PackedFace
