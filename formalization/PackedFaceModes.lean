import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The signed Fourier amplitude for two translated copies of a packed triple. -/

noncomputable section

namespace GaussianChains.PackedFace

open scoped ComplexConjugate

/-- Unit Fourier wave at the normalized position `x`. -/
def wave (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)

private theorem wave_add (n : ℕ) (x y : ℝ) :
    wave n (x + y) = wave n x * wave n y := by
  unfold wave
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem wave_zero (n : ℕ) : wave n 0 = 1 := by simp [wave]

private theorem wave_half (n : ℕ) : wave n (1/2) = (((-1 : ℝ)^n : ℝ) : ℂ) := by
  unfold wave
  rw [show (2 * Real.pi * (n : ℝ) * (1 / 2)) = (n : ℝ) * Real.pi by ring]
  push_cast
  rw [mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private theorem norm_wave (n : ℕ) (x : ℝ) : ‖wave n x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem wave_re (n : ℕ) (x : ℝ) :
    (wave n x).re = Real.cos (2 * Real.pi * n * x) :=
  Complex.exp_ofReal_mul_I_re _

private theorem triple_factor (n : ℕ) (h : ℝ) :
    1 - wave n h + wave n (2*h) =
      wave n h * ((2 * Real.cos (2 * Real.pi * n * h) - 1 : ℝ) : ℂ) := by
  have hz := Complex.add_conj (wave n h)
  have hn := Complex.mul_conj (wave n h)
  rw [Complex.normSq_eq_norm_sq, norm_wave] at hn
  rw [wave_re] at hz
  rw [two_mul, wave_add, Complex.ofReal_sub, ← hz]
  push_cast at hn ⊢
  linear_combination -hn

/-- The formula for the squared norm of the difference between two unit phases. -/
private theorem norm_diff_wave (n : ℕ) (t : ℝ) :
    ‖1 - wave n (1/2+t)‖ ^ 2 =
      2 * (1 - (-1 : ℝ)^n * Real.cos (2 * Real.pi * n * t)) := by
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq (wave n _),
    norm_wave, one_mul, Complex.conj_re, wave_add, wave_half]
  simp only [Complex.normSq_one, one_pow, Complex.re_ofReal_mul, wave_re]
  ring

/-- All six signed positions, with the two triples in the paper's labeling, for every mode. -/
theorem norm_six_wave_sq (n : ℕ) (h t : ℝ) :
    ‖wave n 0 - wave n h + wave n (2*h) - wave n (1/2+t) +
         wave n (1/2+t+h) - wave n (1/2+t+2*h)‖ ^ 2 =
      2 * (2 * Real.cos (2 * Real.pi * n * h) - 1)^2 *
        (1 - (-1 : ℝ)^n * Real.cos (2 * Real.pi * n * t)) := by
  have hf :
      wave n 0 - wave n h + wave n (2*h) - wave n (1/2+t) +
          wave n (1/2+t+h) - wave n (1/2+t+2*h) =
        (1 - wave n h + wave n (2*h)) * (1 - wave n (1/2+t)) := by
    rw [wave_zero, wave_add n (1/2+t) h, wave_add n (1/2+t) (2*h)]
    ring
  rw [hf, triple_factor, norm_mul, norm_mul, norm_wave, one_mul,
    mul_pow, norm_diff_wave, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end GaussianChains.PackedFace

