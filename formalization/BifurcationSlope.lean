import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform sign of the centered, packed-triple branch derivative.
Pairing the two sine waves in each odd mode removes the common zero at h=1/6. -/
noncomputable section
namespace GaussianChains.Bifurcation

private theorem sine_multiple (n : ℕ) (z : ℝ) :
    |Real.sin (n * z)| ≤ (n : ℝ) * |Real.sin z| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin (n * z) * Real.cos z| + |Real.cos (n * z) * Real.sin z| := abs_add_le _ _
      _ ≤ (n : ℝ) * |Real.sin z| * 1 + 1 * |Real.sin z| := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul ih (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
            (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right
            (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (abs_nonneg _))
      _ = _ := by ring

private theorem cosine_odd_multiple (k : ℕ) (z : ℝ) :
    |Real.cos ((2*k+1:ℕ) * z)| ≤ ((2*k+1:ℕ):ℝ) * |Real.cos z| := by
  have hb := sine_multiple (2*k+1) (Real.pi/2-z)
  have harg : ((2*k+1:ℕ):ℝ)*(Real.pi/2-z) =
      (Real.pi/2-((2*k+1:ℕ):ℝ)*z) + (k:ℝ)*Real.pi := by push_cast; ring
  rw [harg, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two_sub, Real.sin_pi_div_two_sub] at hb
  simpa [abs_mul, abs_pow] using hb

def slopeFactor (z : ℝ) : ℝ := (2 * Real.cos z - 1) * Real.sin z

private theorem slopeFactor_eq (z : ℝ) :
    slopeFactor z = 2 * Real.cos (3*z/2) * Real.sin (z/2) := by
  have h := Real.sin_sub_sin (2*z) z
  rw [Real.sin_two_mul] at h
  unfold slopeFactor
  convert h using 1 <;> try ring


theorem slopeFactor_odd_bound (k : ℕ) (z : ℝ) :
    |slopeFactor (((2*k+1:ℕ):ℝ)*z)| ≤ ((2*k+1:ℕ):ℝ)^2 * |slopeFactor z| := by
  let n : ℕ := 2*k+1
  change |slopeFactor ((n:ℝ)*z)| ≤ (n:ℝ)^2 * |slopeFactor z|
  rw [slopeFactor_eq, slopeFactor_eq z, show 3*((n:ℝ)*z)/2 = n*(3*z/2) by ring,
    show (n:ℝ)*z/2 = n*(z/2) by ring]
  simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hh := mul_le_mul (cosine_odd_multiple k (3*z/2)) (sine_multiple n (z/2))
    (abs_nonneg _) (by positivity)
  change |Real.cos (n*(3*z/2))| * |Real.sin (n*(z/2))| ≤
    ((n:ℝ)*|Real.cos (3*z/2)|) * (n*|Real.sin (z/2)|) at hh
  linarith

private theorem odd_growth (k : ℕ) : ((2*k+3:ℕ):ℝ) ≤ 3*2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    push_cast at ih ⊢
    rw [pow_succ]
    linarith [Nat.cast_nonneg (α := ℝ) k]

/-- All odd modes from n=3 onward are dominated by a summable geometric sequence.
The factor q is retained so the bound also applies as the width tends to zero. -/
theorem odd_weight_tail (k : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    ((2*k+3:ℕ):ℝ)^3 * q^((2*k+3)^2) ≤
      (27/256 : ℝ) * q * (1/2:ℝ)^k := by
  let n := 2*k+3
  have hn : 4*k+8 ≤ n^2-1 := by
    dsimp [n]
    have hi : (1:ℕ) + (4*k+8) ≤ (2*k+3)^2 := by nlinarith [Nat.zero_le (k^2)]
    omega
  have hpow : q^(n^2) ≤ q * (1/2:ℝ)^(4*k+8) := by
    have hn' : n^2 = 1+(n^2-1) := by
      dsimp [n]
      have : 0 < (2*k+3)^2 := by positivity
      omega
    calc
      q^(n^2) = q * q^(n^2-1) := by conv_lhs => rw [hn', pow_add, pow_one]
      _ ≤ q * (1/2:ℝ)^(n^2-1) := by gcongr
      _ ≤ q * (1/2:ℝ)^(4*k+8) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hq
  have hN := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) (odd_growth k) 3
  calc
    _ ≤ (3*2^k)^3 * (q * (1/2:ℝ)^(4*k+8)) :=
      mul_le_mul hN hpow (pow_nonneg hq _) (by positivity)
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 3, pow_mul, pow_add, pow_mul]
      ring_nf
      rw [show (1/2:ℝ)=(1/16)*8 by norm_num, mul_pow]
      ring

end GaussianChains.Bifurcation
