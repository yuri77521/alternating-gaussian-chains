import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Fourth-moment width hypothesis of Theorem 1. Index zero is frequency two. -/

noncomputable section
namespace GaussianChains

def widthTerm (q : ℝ) (k : ℕ) : ℝ :=
  ((k + 2 : ℕ) : ℝ) ^ 4 * q ^ ((k + 2) ^ 2 - 1)

def widthR (q : ℝ) : ℝ := ∑' k : ℕ, widthTerm q k

/-- All polynomially weighted Gaussian tails converge throughout the open width range. -/
theorem summable_widthMoment (p : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun k : ℕ => ((k + 2 : ℕ) : ℝ) ^ p * q ^ ((k + 2) ^ 2 - 1)) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one p
    (show ‖q‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ ((summable_nat_add_iff 2).2 hs)
  intro k
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_of_le_one hq0 hq1.le
  have h : k + 2 + 1 ≤ (k + 2)^2 := by nlinarith [Nat.zero_le (k^2)]
  omega

theorem summable_widthTerm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (widthTerm q) := summable_widthMoment 4 hq0 hq1

theorem widthTerm_nonneg {q : ℝ} (hq : 0 ≤ q) (k : ℕ) : 0 ≤ widthTerm q k := by
  unfold widthTerm
  positivity

theorem widthTerm_succ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    widthTerm q (k+1) ≤ widthTerm q k * ((3/2 : ℝ)^4 * q^5) := by
  have hbase : ((k+1+2 : ℕ) : ℝ) ≤ ((k+2 : ℕ) : ℝ) * (3/2) := by
    push_cast
    linarith [show (0 : ℝ) ≤ k by positivity]
  have hpoly := pow_le_pow_left₀ (by positivity) hbase 4
  rw [mul_pow] at hpoly
  have hsq : (k + 1 + 2)^2 = (k+2)^2 + (2*k+5) := by ring
  have hpos : 0 < (k+2)^2 := by positivity
  have hexp : (k+1+2)^2-1 = ((k+2)^2-1) + (2*k+5) := by omega
  have hqtail := pow_le_pow_of_le_one hq0 hq1 (show 5 ≤ 2*k+5 by omega)
  unfold widthTerm
  rw [hexp, pow_add]
  calc
    _ ≤ ((((k+2 : ℕ) : ℝ)^4) * (3/2)^4) *
          (q^((k+2)^2-1) * q^5) :=
      mul_le_mul hpoly (mul_le_mul_of_nonneg_left hqtail (pow_nonneg hq0 _))
        (by positivity) (by positivity)
    _ = _ := by ring

theorem widthTerm_le_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    widthTerm q k ≤ (16 * q^3) * ((3/2 : ℝ)^4 * q^5)^k := by
  induction k with
  | zero => norm_num [widthTerm]
  | succ k ih =>
    rw [pow_succ _ k, ← mul_assoc]
    exact (widthTerm_succ hq0 hq1 k).trans (mul_le_mul_of_nonneg_right ih (by positivity))

/-- The actual infinite fourth-moment tail satisfies the paper's rational bound at 17/50. -/
theorem widthR_lt_two_thirds {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 17/50) :
    widthR q < 2/3 := by
  let qmax : ℝ := 17 / 50
  let r : ℝ := (3/2 : ℝ)^4 * qmax^5
  have hr0 : 0 ≤ r := by norm_num [r, qmax]
  have hr1 : r < 1 := by norm_num [r, qmax]
  have hmajor := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (16*qmax^3)
  have hterm (k : ℕ) : widthTerm q k ≤ (16*qmax^3) * r^k := by
    apply (widthTerm_le_geometric hq0 (by linarith) k).trans
    dsimp [r]
    gcongr
  have h := (summable_widthTerm hq0 (by linarith)).tsum_le_tsum hterm hmajor.summable
  exact h.trans_lt (by rw [hmajor.tsum_eq]; norm_num [r, qmax])

/-- In particular the width hypothesis covers the upper endpoint of Theorem 5. -/
theorem nome_lt_seventeen_fiftieths {s : ℝ} (hs : 0 < s) (hs9 : s ≤ 9) :
    Real.exp (-(Real.pi^2 / s)) < 17/50 := by
  have hπ : (109/100 : ℝ) < Real.pi^2 / s := by
    apply (lt_div_iff₀ hs).2
    nlinarith [sq_nonneg (Real.pi - 3.14), Real.pi_gt_d2]
  have hsum := Real.sum_le_exp_of_nonneg (x := 109/100) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  have hx : (50/17 : ℝ) < Real.exp (Real.pi^2 / s) := by
    exact (by linarith : (50/17 : ℝ) < Real.exp (109/100)).trans (Real.exp_lt_exp.mpr hπ)
  rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos _)]
  linarith

theorem widthR_gaussian_lt_two_thirds {s : ℝ} (hs : 0 < s) (hs9 : s ≤ 9) :
    widthR (Real.exp (-(Real.pi^2) / s)) < 2/3 := by
  rw [neg_div]
  exact widthR_lt_two_thirds (Real.exp_pos _).le (nome_lt_seventeen_fiftieths hs hs9).le

/-- Four times the second-moment tail is bounded by the fourth-moment tail
because the least frequency occurring in either tail is two. -/
theorem secondMomentTail_le_quarter_R {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' k : ℕ, ((k+2 : ℕ) : ℝ)^2 * q^((k+2)^2-1)) ≤ widthR q / 4 := by
  have point (k : ℕ) : 4 * (((k+2 : ℕ) : ℝ)^2 * q^((k+2)^2-1)) ≤ widthTerm q k := by
    unfold widthTerm
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq0 _)
    have hbase : (2 : ℝ) ≤ ((k+2 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hbase 2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg ((k+2:ℕ):ℝ))]
  have h := ((summable_widthMoment 2 hq0 hq1).mul_left 4).tsum_le_tsum point
    (summable_widthTerm hq0 hq1)
  rw [tsum_mul_left] at h
  unfold widthR
  linarith

end GaussianChains
