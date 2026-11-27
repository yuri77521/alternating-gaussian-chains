import ClustersWidth
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp

/-! Analytic upper bound for the score of a dimer box, before multiplying by
the strictly positive physical Fourier prefactor. -/
noncomputable section
namespace GaussianChains.Strip
open Real

theorem nome_cap {s : ℝ} (hs : 0 < s) (h9 : s ≤ 9) : exp (-(π^2)/s) ≤ 17/50 := by
  have hb : (109/100 : ℝ) ≤ π^2/s := by
    apply (le_div_iff₀ hs).mpr
    nlinarith only [h9, Real.pi_gt_d2, sq_nonneg (π-3.14)]
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 109/100) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have he' := he.trans (Real.exp_le_exp.mpr hb)
  rw [neg_div, exp_neg, inv_eq_one_div, div_le_iff₀ (exp_pos _)]
  linarith

/-- At every positive mode the three-dimer bound is 7 n / 5. The first mode
is separated; on the remainder n² ≤ n⁴ / 4 since n ≥ 2. -/
theorem sum_dimer_le {q : ℝ} (hq : 0 < q) (hc : q ≤ 17/50) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hd : ∀ n, a n ≤ 7/5 * (n : ℝ)) :
    (∑' k : ℕ, q^((k+1)^2) * (a (k+1))^2) ≤ q*(343/150) := by
  let f (k : ℕ) := q^((k+1)^2)*(a (k+1))^2
  let d : ℝ := (7/5)^2/4 * q
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hterm (k : ℕ) : f (k+1) ≤ d * widthTerm q k := by
    let n := k+2
    have hn : (2:ℝ) ≤ n := by dsimp [n]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hb := pow_le_pow_left₀ (ha n) (hd n) 2
    have h2 : (4:ℝ) ≤ (n:ℝ)^2 := by nlinarith only [hn, sq_nonneg ((n:ℝ)-2)]
    have h4 := mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr h2)
    have hau : (a n)^2 ≤ (7/5)^2/4 * (n:ℝ)^4 := by nlinarith only [hb,h4]
    have hn0 : 0 < n^2 := by dsimp [n]; positivity
    have hn1 : n^2 = 1 + (n^2-1) := by omega
    change q^(n^2) * (a n)^2 ≤ d*((n:ℝ)^4*q^(n^2-1))
    calc
      _ ≤ q^(n^2) * ((7/5)^2/4*(n:ℝ)^4) :=
        mul_le_mul_of_nonneg_left hau (pow_nonneg hq.le _)
      _ = _ := by conv_lhs => rw [hn1, pow_add, pow_one]
                  dsimp [d]; ring
  have hs := (summable_widthTerm hq.le (by linarith) : Summable (widthTerm q)).mul_left d
  have ht : Summable (fun k : ℕ => f (k+1)) :=
    Summable.of_nonneg_of_le (fun k => by dsimp [f]; positivity) hterm hs
  have hf : Summable f := (summable_nat_add_iff 1).mp ht
  have hsum := ht.tsum_le_tsum hterm hs
  rw [tsum_mul_left] at hsum
  change _ ≤ d * widthR q at hsum
  have hR := mul_le_mul_of_nonneg_left (widthR_lt_two_thirds hq.le hc).le hd0
  have h0 : f 0 ≤ q*(7/5)^2 := by
    simpa [f] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha 1) (hd 1) 2) hq.le
  change (∑' k, f k) ≤ _
  rw [hf.tsum_eq_zero_add]
  dsimp [d] at hR hsum
  linarith

end GaussianChains.Strip
