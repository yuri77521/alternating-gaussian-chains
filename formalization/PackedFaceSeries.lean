import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The Chebyshev series (9) and its first two modewise derivatives. -/
noncomputable section
namespace GaussianChains.PackedFace

open Polynomial.Chebyshev

def amplitude (h : ℝ) (n : ℕ) : ℝ :=
  2 * (T ℝ n).eval (Real.cos (2 * Real.pi * h)) - 1

def phiMode (q h y : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ)^n * q^(n^2-1) * (amplitude h n)^2 * ((T ℝ n).eval (1-y) - 1)

def phiModeD (q h y : ℝ) (n : ℕ) : ℝ :=
  -((-1 : ℝ)^n * q^(n^2-1) * (amplitude h n)^2) * (T ℝ n).derivative.eval (1-y)

def phiModeDD (q h y : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ)^n * q^(n^2-1) * (amplitude h n)^2 * (T ℝ n).derivative.derivative.eval (1-y)

def phi (q h y : ℝ) : ℝ := ∑' k : ℕ, phiMode q h y (k+1)
def phiD (q h y : ℝ) : ℝ := ∑' k : ℕ, phiModeD q h y (k+1)
def phiDD (q h y : ℝ) : ℝ := ∑' k : ℕ, phiModeDD q h y (k+1)

theorem amplitude_eq_cos (h : ℝ) (n : ℕ) :
    amplitude h n = 2 * Real.cos ((n : ℝ) * (2 * Real.pi * h)) - 1 := by
  simp [amplitude]

theorem abs_amplitude_le (h : ℝ) (n : ℕ) : |amplitude h n| ≤ 3 := by
  rw [amplitude_eq_cos, abs_le]
  constructor
  · linarith [Real.neg_one_le_cos ((n : ℝ) * (2 * Real.pi * h))]
  · linarith [Real.cos_le_one ((n : ℝ) * (2 * Real.pi * h))]

theorem hasDerivAt_phiMode (q h y : ℝ) (n : ℕ) :
    HasDerivAt (fun w => phiMode q h w n) (phiModeD q h y n) y := by
  have hi := (hasDerivAt_id y).const_sub (1:ℝ)
  have hp := ((T ℝ n).hasDerivAt (1-y)).comp y hi
  convert (hp.sub_const 1).const_mul ((-1:ℝ)^n * q^(n^2-1) * amplitude h n^2) using 1 <;>
    simp [Function.comp_def, phiMode, phiModeD, mul_assoc]

theorem hasDerivAt_phiModeD (q h y : ℝ) (n : ℕ) :
    HasDerivAt (fun w => phiModeD q h w n) (phiModeDD q h y n) y := by
  have hi := (hasDerivAt_id y).const_sub (1:ℝ)
  have hp := ((T ℝ n).derivative.hasDerivAt (1-y)).comp y hi
  convert hp.const_mul (-((-1:ℝ)^n * q^(n^2-1) * amplitude h n^2)) using 1 <;>
    simp [Function.comp_def, phiModeD, phiModeDD, mul_assoc]

@[simp] theorem phi_zero (q h : ℝ) : phi q h 0 = 0 := by
  simp [phi, phiMode]

end GaussianChains.PackedFace

