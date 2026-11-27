import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Fixed-point enclosures for the exponentials in the real-space Gaussian sums.
We evaluate a cubic at a reduced argument and perform 64 outward-rounded
squarings. Integer division and exact rational arithmetic suffice for replay. -/

namespace GaussianChains.CertExp

private def D : ℕ := 2 ^ 280

private theorem dpos : 0 < D := pow_pos (by decide) _

private def value (v : ℕ) : ℚ := (v : ℚ) / D

private def roundLo (a : ℚ) : ℕ := ⌊max 0 a * D⌋₊
private def roundHi (a : ℚ) : ℕ := ⌈a * D⌉₊

private theorem lo_sound {a : ℚ} {y : ℝ} (ha : (a : ℝ) ≤ y) (hy : 0 ≤ y) :
    ((value (roundLo a) : ℚ) : ℝ) ≤ y := by
  have h := Nat.floor_le (R := ℚ) (mul_nonneg (le_max_left 0 a) (Nat.cast_nonneg D))
  have h' : value (roundLo a) ≤ max 0 a :=
    (div_le_iff₀ (Nat.cast_pos.mpr dpos)).2 h
  exact (by exact_mod_cast h' : ((value (roundLo a) : ℚ) : ℝ) ≤ max 0 (a : ℝ)).trans
    (max_le hy ha)

private theorem hi_sound (a : ℚ) : a ≤ value (roundHi a) := by
  exact (le_div_iff₀ (Nat.cast_pos.mpr dpos)).2 (Nat.le_ceil _)

private def sqLo (v : ℕ) : ℕ := v * v / D
private def sqHi (v : ℕ) : ℕ := v * v / D + 1

private theorem sqLo_sound (v : ℕ) : value (sqLo v) ≤ (value v)^2 := by
  have h : ((sqLo v : ℕ) : ℚ) * D ≤ (v : ℚ) * v := by
    exact_mod_cast Nat.div_mul_le_self (v*v) D
  have hd : (0 : ℚ) < D := Nat.cast_pos.mpr dpos
  unfold value
  rw [div_pow, div_le_div_iff₀ hd (sq_pos_of_pos hd)]
  nlinarith [mul_le_mul_of_nonneg_right h hd.le]

private theorem sqHi_sound (v : ℕ) : (value v)^2 ≤ value (sqHi v) := by
  have h : (v : ℚ) * v ≤ (D : ℚ) * (sqHi v : ℕ) := by
    exact_mod_cast (Nat.lt_mul_div_succ (v*v) dpos).le
  have hd : (0 : ℚ) < D := Nat.cast_pos.mpr dpos
  unfold value
  rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hd) hd]
  nlinarith [mul_le_mul_of_nonneg_right h hd.le]

private def repeated (step : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, v => v
  | n+1, v => repeated step n (step v)

private theorem repeated_sound {l u : ℕ} {y : ℝ}
    (hl : ((value l : ℚ) : ℝ) ≤ Real.exp y)
    (hu : Real.exp y ≤ ((value u : ℚ) : ℝ)) (k : ℕ) :
    ((value (repeated sqLo k l) : ℚ) : ℝ) ≤ Real.exp (2^k * y) ∧
    Real.exp (2^k * y) ≤ ((value (repeated sqHi k u) : ℚ) : ℝ) := by
  induction k generalizing l u y with
  | zero => simpa [repeated] using And.intro hl hu
  | succ k ih =>
    have h₁ : ((value (sqLo l) : ℚ) : ℝ) ≤ ((value l : ℚ) : ℝ)^2 := by
      exact_mod_cast sqLo_sound l
    have h₂ : ((value u : ℚ) : ℝ)^2 ≤ ((value (sqHi u) : ℚ) : ℝ) := by
      exact_mod_cast sqHi_sound u
    have hnon : 0 ≤ ((value l : ℚ) : ℝ) := by
      unfold value
      positivity
    have hl' := h₁.trans (pow_le_pow_left₀ hnon hl 2)
    have hu' := (pow_le_pow_left₀ (Real.exp_pos y).le hu 2).trans h₂
    rw [← Real.exp_nat_mul] at hl' hu'
    have H := ih hl' hu'
    simpa [repeated, pow_succ, mul_assoc] using H

private def cubic (z : ℚ) : ℚ := 1 + z + z^2/2 + z^3/6

private theorem cubic_sound (z : ℚ) (hz : |(z : ℝ)| ≤ 1) :
    ((cubic z - z^4 : ℚ) : ℝ) ≤ Real.exp (z : ℝ) ∧
    Real.exp (z : ℝ) ≤ ((cubic z + z^4 : ℚ) : ℝ) := by
  have h := Real.exp_bound hz (by decide : 0 < 4)
  simp [Finset.sum_range_succ, Nat.factorial_succ] at h
  have h' := abs_le.mp h
  unfold cubic
  push_cast
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (z : ℝ)^4)] at h'
  obtain ⟨ha, hb⟩ := h'
  constructor <;> nlinarith [show 0 ≤ (z : ℝ)^4 by positivity]

/-- Rational enclosure of exp(-x) on 0 ≤ x ≤ 600. -/
def negExpBox (x : ℚ) : ℚ × ℚ :=
  let z := -x / 2^64
  (value (repeated sqLo 64 (roundLo (cubic z - z^4))),
   value (repeated sqHi 64 (roundHi (cubic z + z^4))))

theorem negExpBox_sound {x : ℚ} (hx : 0 ≤ x) (hmax : x ≤ 600) :
    ((negExpBox x).1 : ℝ) ≤ Real.exp (-(x : ℝ)) ∧
    Real.exp (-(x : ℝ)) ≤ ((negExpBox x).2 : ℝ) := by
  let z : ℚ := -x / 2^64
  have hz : |(z : ℝ)| ≤ 1 := by
    have hz' : |z| ≤ 1 := by
      dsimp [z]
      rw [abs_div, abs_neg, abs_of_nonneg hx, abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity)).2
      linarith [show (600 : ℚ) ≤ 2^64 by norm_num]
    exact_mod_cast hz'
  obtain ⟨hl,hu⟩ := cubic_sound z hz
  have hr : ((cubic z + z^4 : ℚ) : ℝ) ≤
      ((value (roundHi (cubic z + z^4)) : ℚ) : ℝ) := by
    exact Rat.cast_le.mpr (hi_sound (cubic z + z^4))
  have H := repeated_sound (l := roundLo (cubic z - z^4)) (u := roundHi (cubic z + z^4))
    (y := (z : ℝ)) (lo_sound (a := cubic z - z^4) hl (Real.exp_pos _).le) (hu.trans hr) 64
  have he : (2 : ℝ)^64 * (z : ℝ) = -(x : ℝ) := by
    dsimp [z]
    push_cast
    ring
  rwa [he] at H

/-- Two endpoint evaluations enclose an entire interval of Gaussian exponents. -/
def negExpRange (lo hi : ℚ) : ℚ × ℚ := ((negExpBox hi).1, (negExpBox lo).2)

theorem negExpRange_sound {lo hi : ℚ} {x : ℝ}
    (h₀ : 0 ≤ lo) (h₁ : hi ≤ 600)
    (hl : (lo : ℝ) ≤ x) (hu : x ≤ (hi : ℝ)) :
    ((negExpRange lo hi).1 : ℝ) ≤ Real.exp (-x) ∧
    Real.exp (-x) ≤ ((negExpRange lo hi).2 : ℝ) := by
  have hor : lo ≤ hi := Rat.cast_le.mp (hl.trans hu)
  exact ⟨(negExpBox_sound (h₀.trans hor) h₁).1.trans (Real.exp_le_exp.mpr (neg_le_neg hu)),
    (Real.exp_le_exp.mpr (neg_le_neg hl)).trans (negExpBox_sound h₀ (hor.trans h₁)).2⟩

end GaussianChains.CertExp
