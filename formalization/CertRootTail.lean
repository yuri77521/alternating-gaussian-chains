import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform, two-sided image-tail estimates at the isolated width 22. -/
noncomputable section

namespace GaussianChains.Root22

set_option exponentiation.threshold 512

def image (x : ℝ) (k : ℤ) : ℝ := Real.exp (-22 * (x + k)^2)

def term (x : ℝ) (k : ℤ) : ℝ := -44 * (x + k) * image x k

def derivKernel (x : ℝ) : ℝ := ∑' k, term x k

def finiteKernel (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc (-4 : ℤ) 4, term x k

def tailWeight (n : ℕ) : ℝ := 44 * (1/2:ℝ)^300 * (1/2:ℝ)^n

private theorem half_exp : Real.exp (-1) ≤ (1/2:ℝ) := by
  rw [Real.exp_neg, one_div]
  apply (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 2)).2
  linarith [Real.add_one_le_exp 1]

private theorem envelope (n : ℕ) (u : ℝ) (hu : 4 + (n:ℝ) ≤ |u|) :
    Real.exp (|u| - 22 * u^2) ≤ (1/2:ℝ)^300 * (1/2:ℝ)^n := by
  have h₁ : 4 ≤ |u| := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h₂ : |u| - 22*u^2 ≤ (300:ℝ)*(-1) + (n:ℝ)*(-1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (by linarith : 0 ≤ |u| + 4),
      mul_nonneg (sub_nonneg.mpr h₁) (by linarith : 0 ≤ |u| + 3), sq_abs u]
  refine (Real.exp_le_exp.mpr h₂).trans ?_
  rw [Real.exp_add, show (300:ℝ) = ((300:ℕ):ℝ) by norm_num, Real.exp_nat_mul, Real.exp_nat_mul]
  gcongr <;> exact half_exp

theorem bounds_at_image (x : ℝ) (k : ℤ) (n : ℕ) (h : 4 + (n:ℝ) ≤ |x + k|) :
    |term x k| ≤ tailWeight n ∧ |image x k| ≤ tailWeight n := by
  have he := envelope n (x+k) h
  rw [sub_eq_add_neg, Real.exp_add] at he
  rw [← neg_mul] at he
  change Real.exp |x+k| * image x k ≤ _ at he
  have hpos : 0 ≤ image x k := Real.exp_nonneg _
  have ha : |x+k| ≤ Real.exp |x+k| := by linarith [Real.add_one_le_exp |x+k|]
  have hh : 1 ≤ Real.exp |x+k| := Real.one_le_exp (abs_nonneg _)
  constructor
  · unfold term
    rw [abs_mul, abs_mul, abs_of_nonneg hpos]
    norm_num
    calc
      44 * |x + ↑k| * image x k ≤ 44 * (Real.exp |x+k| * image x k) := by
        rw [mul_assoc]; gcongr
      _ ≤ _ := by unfold tailWeight; rw [mul_assoc]; gcongr
  · rw [abs_of_nonneg hpos]
    have hzero : 0 ≤ (1/2:ℝ)^300 * (1/2:ℝ)^n := by positivity
    have h' := mul_le_mul_of_nonneg_right hh hpos
    unfold tailWeight
    rw [mul_assoc]
    linarith

private theorem abs_pos_index {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    4 + (n:ℝ) ≤ |x + ((n:ℤ) + 5 : ℤ)| := by
  push_cast
  exact le_trans (by linarith [(abs_le.mp hx).1]) (le_abs_self _)

private theorem abs_neg_index {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    4 + (n:ℝ) ≤ |x + (-((n:ℤ) + 5) : ℤ)| := by
  push_cast
  exact le_trans (by linarith [(abs_le.mp hx).2]) (neg_le_abs _)

theorem tailWeight_summable : Summable tailWeight :=
  (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)).mul_left _

theorem tailWeight_sum : ∑' n, tailWeight n = 88 * (1/2:ℝ)^300 := by
  simp only [tailWeight, tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)]
  ring

private theorem bound_side {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ tailWeight n) :
    Summable a ∧ |∑' n, a n| ≤ 88 * (1/2:ℝ)^300 := by
  have hsum : Summable a := .of_norm_bounded tailWeight_summable (by simpa only [Real.norm_eq_abs])
  refine ⟨hsum, ?_⟩
  rw [← Real.norm_eq_abs, ← tailWeight_sum]
  have hn : Summable (fun n => ‖a n‖) := .of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using ha n) tailWeight_summable
  apply (norm_tsum_le_tsum_norm hn).trans
  exact hn.tsum_le_tsum (by simpa only [Real.norm_eq_abs]) tailWeight_summable

/-- The nine central images and the two Gaussian tails partition every integer exactly once. -/
theorem split_images (a : ℤ → ℝ)
    (hp : Summable fun n : ℕ => a ((n:ℤ)+5))
    (hm : Summable fun n : ℕ => a (-((n:ℤ)+5))) :
    ∑' k, a k = (∑ k ∈ Finset.Icc (-4:ℤ) 4, a k) +
      (∑' n : ℕ, a ((n:ℤ)+5)) + (∑' n : ℕ, a (-((n:ℤ)+5))) := by
  have hp' : Summable (fun n : ℕ => a (n:ℤ)) :=
    (summable_nat_add_iff 5).mp (by simpa using hp)
  have hm' : Summable (fun n : ℕ => a (-((n:ℤ)+1))) :=
    (summable_nat_add_iff 4).mp (by simpa [add_assoc] using hm)
  rw [tsum_of_nat_of_neg_add_one hp' hm', ← hp'.sum_add_tsum_nat_add 5,
    ← hm'.sum_add_tsum_nat_add 4]
  have hc : Finset.Icc (-4:ℤ) 4 = {-4,-3,-2,-1,0,1,2,3,4} := by decide
  simp [hc, Finset.sum_range_succ, add_assoc]
  ring

theorem finite_tail {a : ℤ → ℝ}
    (hp : ∀ n : ℕ, |a ((n:ℤ)+5)| ≤ tailWeight n)
    (hm : ∀ n : ℕ, |a (-((n:ℤ)+5))| ≤ tailWeight n) :
    |(∑' k, a k) - ∑ k ∈ Finset.Icc (-4:ℤ) 4, a k| ≤ 1 / 10^50 := by
  obtain ⟨sp, bp⟩ := bound_side hp
  obtain ⟨sm, bm⟩ := bound_side hm
  rw [split_images a sp sm, add_assoc, add_sub_cancel_left]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ (88 * (1/2:ℝ)^300) + 88 * (1/2:ℝ)^300 := add_le_add bp bm
    _ ≤ _ := by norm_num

theorem tail_bound {x : ℝ} (hx : |x| ≤ 1) :
    |derivKernel x - finiteKernel x| ≤ 1 / 10^50 :=
  finite_tail (fun n => (bounds_at_image _ _ _ (abs_pos_index hx n)).1)
    (fun n => (bounds_at_image _ _ _ (abs_neg_index hx n)).1)

theorem image_tail_bound {x : ℝ} (hx : |x| ≤ 1) :
    |(∑' k, image x k) - ∑ k ∈ Finset.Icc (-4:ℤ) 4, image x k| ≤ 1 / 10^50 :=
  finite_tail (fun n => (bounds_at_image _ _ _ (abs_pos_index hx n)).2)
    (fun n => (bounds_at_image _ _ _ (abs_neg_index hx n)).2)

private def major (k : ℤ) : ℝ :=
  if k.natAbs < 5 then 264 else tailWeight (k.natAbs-5)

private theorem pos_major (n : ℕ) : major ((n:ℤ)+5) = tailWeight n := by
  change (if (n+5:ℕ) < 5 then _ else tailWeight (n+5-5)) = _
  simp

private theorem neg_major (n : ℕ) : major (-((n:ℤ)+5)) = tailWeight n := by
  unfold major
  rw [Int.natAbs_neg]
  exact pos_major n

private theorem major_summable : Summable major := by
  apply Summable.of_nat_of_neg_add_one
  · apply (summable_nat_add_iff 5).1
    simpa [Nat.cast_add, pos_major] using tailWeight_summable
  · apply (summable_nat_add_iff 4).1
    refine tailWeight_summable.congr (fun n => ?_)
    rw [← neg_major n]
    congr 2

private theorem major_bounds {x : ℝ} (hx : |x| ≤ 1) (k : ℤ) :
    ‖term x k‖ ≤ major k ∧ ‖image x k‖ ≤ major k := by
  have hac : (k.natAbs:ℝ) = |(k:ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    simp
  simp only [Real.norm_eq_abs]
  unfold major
  split_ifs with hk
  · have hkn : (k.natAbs:ℝ) < 5 := by exact_mod_cast hk
    have hu : |x + (k:ℝ)| ≤ 6 := by
      have := abs_add_le x (k:ℝ)
      linarith
    have he : |image x k| ≤ 1 := by
      rw [image, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [sq_nonneg (x + (k:ℝ))]
    constructor
    · calc
        _ = 44 * |x+(k:ℝ)| * |image x k| := by simp [term, abs_mul]
        _ ≤ 44 * 6 * 1 := by gcongr
        _ = _ := by norm_num
    · linarith
  · apply bounds_at_image
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat, hac]
    have hdiff := abs_add_le (x + (k:ℝ)) (-x)
    rw [show x + (k:ℝ) + -x = (k:ℝ) by ring, abs_neg] at hdiff
    linarith

theorem continuousOn_derivKernel : ContinuousOn derivKernel (Set.Icc (-1:ℝ) 1) := by
  apply continuousOn_tsum (u := major)
  · intro k
    unfold term image
    fun_prop
  · exact major_summable
  · exact fun k x hx => (major_bounds (abs_le.mpr hx) k).1

theorem hasDerivAt_image (x : ℝ) (k : ℤ) :
    HasDerivAt (fun y => image y k) (term x k) x := by
  have h := (((hasDerivAt_id x).add_const (k:ℝ)).pow 2).const_mul (-22)
  convert h.exp using 1 <;> simp [image, term] <;> ring

/-- On the interior of the tail-bound interval, differentiate the full image sum termwise. -/
theorem hasDerivAt_imageSum {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y => ∑' k, image y k) (derivKernel x) x := by
  apply hasDerivAt_tsum_of_isPreconnected (u := major) (t := Set.Ioo (-1:ℝ) 1)
    (y₀ := 0) major_summable isOpen_Ioo isPreconnected_Ioo (fun k y _ => hasDerivAt_image y k)
  · exact fun k y hy => (major_bounds (abs_le.mpr ⟨hy.1.le, hy.2.le⟩) k).1
  · constructor <;> norm_num
  · exact .of_norm_bounded major_summable (fun k => (major_bounds (by norm_num : |(0:ℝ)| ≤ 1) k).2)
  · exact hx

/-- Reflection about a half period makes the exact derivative odd. -/
theorem derivKernel_one_sub (x : ℝ) : derivKernel (1-x) = -derivKernel x := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun k => -k-1, invFun := fun k => -k-1,
      left_inv := fun k => by dsimp; ring, right_inv := fun k => by dsimp; ring }
  have href (k : ℤ) : term (1-x) k = -term x (e k) := by
    unfold term image
    dsimp [e]
    push_cast
    rw [show x + (-(k:ℝ)-1) = -(1-x+k) by ring, neg_sq]
    ring
  simp only [derivKernel, href, tsum_neg, e.tsum_eq]

end GaussianChains.Root22

