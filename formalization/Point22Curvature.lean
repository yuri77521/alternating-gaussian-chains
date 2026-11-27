import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Second derivative image formula and two-image enclosure for the local curvature tests. -/
noncomputable section
namespace GaussianChains.Point22.Curvature
open Set

def gaussian₂ (u : ℝ) : ℝ := (1936*u^2 - 44) * Real.exp (-22*u^2)

def kernel₂ (x : ℝ) : ℝ := ∑' k : ℤ, gaussian₂ (x+k)

theorem kernel₂_one_sub (x : ℝ) : kernel₂ (1-x) = kernel₂ x := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun k => -k-1, invFun := fun k => -k-1,
      left_inv := fun k => by dsimp; ring, right_inv := fun k => by dsimp; ring }
  have href (k : ℤ) : gaussian₂ (1-x+k) = gaussian₂ (x+(e k:ℤ)) := by
    unfold gaussian₂
    dsimp [e]; push_cast
    rw [show x + (-(k:ℝ)-1) = -(1-x+k) by ring, neg_sq]
  simp only [kernel₂, href]
  exact e.tsum_eq (fun k : ℤ => gaussian₂ (x+k))

private def weight (n : ℕ) : ℝ := 2000 * (1/2:ℝ)^20 * (1/2:ℝ)^n

private theorem weight_summable : Summable weight :=
  (summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)).mul_left _

private theorem weight_sum : ∑' n, weight n = 4000 * (1/2:ℝ)^20 := by
  simp only [weight, tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)]
  ring

private theorem omitted_image_bound {u : ℝ} {n : ℕ} (hu : 1+(n:ℝ) ≤ |u|) :
    |gaussian₂ u| ≤ weight n ∧ |-44 * u * Real.exp (-22*u^2)| ≤ weight n := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have h1 : 1 ≤ |u| := by linarith
  have he : 2*|u| - 22*u^2 ≤ -(20:ℝ) + (n:ℝ)*(-1) := by
    nlinarith only [hu, sq_abs u, mul_nonneg (sub_nonneg.mpr h1) (abs_nonneg u)]
  have half_bound : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg, one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 2)).2
    linarith [Real.add_one_le_exp 1]
  have hen : Real.exp (2*|u|) * Real.exp (-22*u^2) ≤ (1/2:ℝ)^20*(1/2:ℝ)^n := by
    rw [← Real.exp_add]
    apply (Real.exp_le_exp.mpr (show 2*|u| + -22*u^2 ≤ -(20:ℝ) + (n:ℝ)*(-1) by linarith only [he])).trans
    rw [Real.exp_add, show -(20:ℝ)=((20:ℕ):ℝ)*(-1) by norm_num, Real.exp_nat_mul,
      Real.exp_nat_mul]
    gcongr
  have hea : 1 ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg _)
  have hab : |u| ≤ Real.exp |u| := by linarith only [Real.add_one_le_exp |u|]
  have hsq : u^2 ≤ Real.exp (2*|u|) := by
    rw [two_mul, Real.exp_add, ← sq, ← sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg _) hab 2
  have h2 : 1 ≤ Real.exp (2*|u|) := Real.one_le_exp (by positivity)
  have h3 : |u| ≤ Real.exp (2*|u|) :=
    hab.trans (Real.exp_le_exp.mpr (by linarith [abs_nonneg u]))
  have hc : |1936*u^2-44| ≤ 2000*Real.exp (2*|u|) := by
    apply abs_le.mpr
    constructor <;> linarith only [hsq,h2,sq_nonneg u]
  have hd : |-44*u| ≤ 2000*Real.exp (2*|u|) := by
    rw [abs_mul]
    norm_num
    linarith only [h3, h2]
  have bound {A : ℝ} (hA : |A| ≤ 2000*Real.exp (2*|u|)) :
      |A * Real.exp (-22*u^2)| ≤ weight n := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    unfold weight
    nlinarith only [mul_le_mul_of_nonneg_right hA (Real.exp_pos (-22*u^2)).le, hen]
  exact ⟨bound hc,bound hd⟩

private theorem omitted_sum {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ weight n) :
    Summable a ∧ |∑' n, a n| ≤ 4000*(1/2:ℝ)^20 := by
  have hn : Summable (fun n => ‖a n‖) := Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (by simpa only [Real.norm_eq_abs] using ha) weight_summable
  refine ⟨hn.of_norm,?_⟩
  rw [← Real.norm_eq_abs, ← weight_sum]
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (by simpa only [Real.norm_eq_abs] using ha) weight_summable)

private def leftTail (x : ℝ) (n : ℕ) := gaussian₂ (x - ((n:ℝ)+2))
private def rightTail (x : ℝ) (n : ℕ) := gaussian₂ (x + ((n:ℝ)+1))

private theorem tail_args {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (n : ℕ) :
    (1+(n:ℝ) ≤ |x-((n:ℝ)+2)|) ∧ (1+(n:ℝ) ≤ |x+((n:ℝ)+1)|) :=
  ⟨le_trans (by linarith [hx.2]) (neg_le_abs _),
   le_trans (by linarith [hx.1]) (le_abs_self _)⟩

private theorem kernel₂_remainder {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    kernel₂ x - (gaussian₂ x + gaussian₂ (x-1)) =
      (∑' n, rightTail x n) + ∑' n, leftTail x n := by
  let A := fun k : ℤ => gaussian₂ (x+k)
  have hp := (omitted_sum fun n => (omitted_image_bound (tail_args hx n).2).1).1
  have hm := (omitted_sum fun n => (omitted_image_bound (tail_args hx n).1).1).1
  have sp' : Summable fun n : ℕ => A (n:ℤ) := by
    apply (summable_nat_add_iff 1).1
    simpa [A, rightTail, Nat.cast_add] using hp
  have sm' : Summable fun n : ℕ => A (-((n:ℤ)+1)) := by
    apply (summable_nat_add_iff 1).1
    simpa [A, leftTail, Nat.cast_add, add_assoc, sub_eq_add_neg] using hm
  change (∑' k, A k) - _ = _
  rw [tsum_of_nat_of_neg_add_one sp' sm', ← sp'.sum_add_tsum_nat_add 1, ← sm'.sum_add_tsum_nat_add 1]
  simp [A, leftTail, rightTail, add_assoc, sub_eq_add_neg]
  abel

/-- For every point of the closed unit cell, only the central and preceding image are
needed to enclose the second derivative to within one hundredth. -/
theorem kernel₂_two_images {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |kernel₂ x - (gaussian₂ x + gaussian₂ (x-1))| ≤ 1/100 := by
  rw [kernel₂_remainder hx]
  have hp := (omitted_sum fun n => (omitted_image_bound (tail_args hx n).2).1).2
  have hm := (omitted_sum fun n => (omitted_image_bound (tail_args hx n).1).1).2
  exact ((abs_add_le _ _).trans (add_le_add hp hm)).trans (by norm_num)

private theorem gaussian₂_pos {u : ℝ} (hu : 1 ≤ |u|) : 0 < gaussian₂ u := by
  apply mul_pos _ (Real.exp_pos _)
  nlinarith [sq_abs u, mul_nonneg (sub_nonneg.mpr hu) (abs_nonneg u)]

theorem kernel₂_two_images_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    0 ≤ kernel₂ x - (gaussian₂ x + gaussian₂ (x-1)) := by
  rw [kernel₂_remainder hx]
  apply add_nonneg <;> apply tsum_nonneg <;> intro n <;> apply (gaussian₂_pos _).le
  · linarith [(tail_args hx n).2, Nat.cast_nonneg (α := ℝ) n]
  · linarith [(tail_args hx n).1, Nat.cast_nonneg (α := ℝ) n]

end GaussianChains.Point22.Curvature
