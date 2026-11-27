import StripSplitGain

/-! Real powers of the two six-site trial configurations at one frequency. -/
noncomputable section
namespace GaussianChains.Strip
open Real
def fivePower (η v : ℝ) (n : ℕ) : ℝ :=
  (five (n*η))^2+1-2*(-1:ℝ)^n*five (n*η)*cos (n*v)

def triplePower (η : ℝ) (n : ℕ) : ℝ :=
  2*(triple (n*η))^2*(1-(-1:ℝ)^n)

theorem abs_five_le (w : ℝ) : |five w| ≤ 5 := by
  unfold five
  rw [abs_le]
  constructor <;> linarith [Real.neg_one_le_cos w,Real.cos_le_one w,
    Real.neg_one_le_cos (2*w),Real.cos_le_one (2*w)]

theorem fivePower_nonneg (η v : ℝ) (n : ℕ) : 0 ≤ fivePower η v n := by
  have he : |(-1:ℝ)^n*cos (n*v)| ≤ 1 := by simpa [abs_mul,abs_pow] using abs_cos_le_one (n*v)
  have hsq := sq_nonneg (five (n*η)-(-1:ℝ)^n*cos (n*v))
  have h := pow_le_pow_left₀ (abs_nonneg _) he 2
  rw [sq_abs] at h
  unfold fivePower
  nlinarith only [hsq,h]

theorem fivePower_le_square (η v : ℝ) (n : ℕ) :
    fivePower η v n ≤ (1+|five (n*η)|)^2 := by
  have h : |((-1:ℝ)^n*five (n*η))*cos (n*v)| ≤ |five (n*η)| := by
    rw [abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one (n*v)) (abs_nonneg (five (n*η)))
  have hm := (abs_le.mp h).1
  unfold fivePower
  nlinarith only [hm,sq_abs (five (n*η))]

theorem fivePower_le (η v : ℝ) (n : ℕ) : fivePower η v n ≤ 36 := by
  apply (fivePower_le_square η v n).trans
  have h := abs_five_le (n*η)
  exact (pow_le_pow_left₀ (by positivity) (by linarith : 1+|five (n*η)| ≤ 6) 2).trans_eq (by norm_num)

theorem triplePower_bounds (η : ℝ) (n : ℕ) : 0 ≤ triplePower η n ∧ triplePower η n ≤ 36 := by
  have hb : |triple (n*η)| ≤ 3 := by
    apply abs_le.mpr; unfold triple
    constructor <;> linarith [Real.neg_one_le_cos (n*η),Real.cos_le_one (n*η)]
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hs
  rcases neg_one_pow_eq_or ℝ n with h|h <;> rw [triplePower,h] <;>
    constructor <;> nlinarith [sq_nonneg (triple (n*η))]

end GaussianChains.Strip
