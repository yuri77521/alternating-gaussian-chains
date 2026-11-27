import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Intervals

/-! The nearest endpoint index is monotone along ordered lifts and advances
by two over one period. Its middle level is a contiguous cyclic cluster.
The sign of the rounded first moment forces this level to have odd length. -/
noncomputable section
namespace GaussianChains.JumpLocalization
open Real Finset

def endpointIndex (θ : ℕ → ℝ) (n : ℕ) : ℤ := round (θ n / π)

theorem endpointIndex_monotone {θ : ℕ → ℝ} (hθ : Monotone θ) : Monotone (endpointIndex θ) := by
  intro i j hij
  simp only [endpointIndex, round_eq]
  apply Int.floor_mono
  linarith [div_le_div_of_nonneg_right (hθ hij) pi_pos.le]

theorem endpointIndex_period {θ : ℕ → ℝ} {N : ℕ} (hp : ∀ n, θ (n+N) = θ n + 2*π) (n : ℕ) :
    endpointIndex θ (n+N) = endpointIndex θ n + 2 := by
  simp only [endpointIndex, hp]
  rw [show (θ n + 2*π)/π = θ n/π+2 by field_simp [pi_ne_zero]]
  exact round_add_ofNat _ _

theorem endpointIndex_nearest (θ : ℕ → ℝ) (n : ℕ) (k : ℤ) :
    |θ n - (endpointIndex θ n : ℝ)*π| ≤ |θ n - (k:ℝ)*π| := by
  have e (v : ℤ) : |θ n / π - (v : ℝ)| * π = |θ n - (v:ℝ)*π| := by
    calc
      _ = |(θ n/π - (v:ℝ))*π| := by rw [abs_mul, abs_of_pos pi_pos]
      _ = _ := by congr 1; field_simp
  rw [← e, ← e]
  exact mul_le_mul_of_nonneg_right (round_le (θ n / π) k) pi_pos.le

private theorem alt_sum (n : ℕ) : ∑ j ∈ range n, (-1:ℝ)^j = (1-(-1:ℝ)^n)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

private theorem cos_endpoint_succ (k : ℤ) : cos (((k+1:ℤ):ℝ)*π) = -cos ((k:ℝ)*π) := by
  push_cast
  rw [add_mul, one_mul, cos_add_pi]

private theorem cos_endpoint_two (k : ℤ) : cos (((k+2:ℤ):ℝ)*π) = cos ((k:ℝ)*π) := by
  push_cast
  rw [add_mul, cos_add_two_pi]

/-- If the alternating moment at the nearest endpoints is nonzero, the
middle level in the period has odd cardinality. -/
theorem odd_middle_level {m : ℕ} (v : ℕ → ℤ) (hv : Monotone v)
    (hp : v (2*m) = v 0 + 2)
    (hm : (∑ j ∈ range (2*m), (-1:ℝ)^j * cos ((v j : ℝ)*π)) ≠ 0) :
    ∃ a b : ℕ, a ≤ b ∧ b ≤ 2*m ∧ (b-a)%2=1 ∧
      (∀ j < a, v j = v 0) ∧
      (∀ j, a ≤ j → j < b → v j = v 0+1) ∧
      (∀ j, b ≤ j → j ≤ 2*m → v j = v 0+2) := by
  classical
  have H₁ : ∃ n, v 0+1 ≤ v n := ⟨2*m, by omega⟩
  have H₂ : ∃ n, v 0+2 ≤ v n := ⟨2*m, hp.ge⟩
  let a := Nat.find H₁
  let b := Nat.find H₂
  have ha : v 0+1 ≤ v a := Nat.find_spec H₁
  have hb : v 0+2 ≤ v b := Nat.find_spec H₂
  have hab : a ≤ b := Nat.find_min' H₁ (by omega)
  have hbm : b ≤ 2*m := Nat.find_min' H₂ hp.ge
  have left (j : ℕ) (hj : j < a) : v j = v 0 := by
    have h₁ := Nat.find_min H₁ hj
    have h₂ := hv (Nat.zero_le j)
    omega
  have middle (j : ℕ) (hj : a ≤ j) (hj' : j < b) : v j = v 0 + 1 := by
    have h₁ := Nat.find_min H₂ hj'
    have h₂ := hv hj
    omega
  have right (j : ℕ) (hj : b ≤ j) (hj' : j ≤ 2*m) : v j = v 0 + 2 := by
    have := hv hj
    have := hv hj'
    omega
  refine ⟨a, b, hab, hbm, ?_, left, middle, right⟩
  by_contra hh
  apply hm
  let c := cos ((v 0 : ℝ)*π)
  have site (j : ℕ) (hj : j < 2*m) :
      (-1:ℝ)^j * cos ((v j : ℝ)*π) =
      (-1:ℝ)^j * c - if a ≤ j ∧ j < b then 2*((-1:ℝ)^j*c) else 0 := by
    by_cases hja : j < a
    · simp [left j hja, c, not_le.mpr hja]
    by_cases hjb : j < b
    · rw [middle j (not_lt.mp hja) hjb, if_pos ⟨not_lt.mp hja,hjb⟩, cos_endpoint_succ]
      dsimp [c]; ring
    · rw [right j (not_lt.mp hjb) hj.le, if_neg (fun h => hjb h.2), cos_endpoint_two]
      simp [c]
  have hset : (range (2*m)).filter (fun j => a ≤ j ∧ j < b) = Ico a b := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [sum_congr rfl (fun j hj => site j (mem_range.mp hj)), sum_sub_distrib, ← sum_filter, hset,
    ← Finset.mul_sum, Finset.sum_Ico_eq_sub _ hab, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_mul, alt_sum, alt_sum, alt_sum]
  have hpw : (-1:ℝ)^b = (-1:ℝ)^a := by
    rw [neg_one_pow_eq_pow_mod_two b, neg_one_pow_eq_pow_mod_two a]
    congr 1
    omega
  rw [hpw, pow_mul]
  norm_num

/-- Replacing each cosine by the cosine at its nearest endpoint loses at
most one angular localization radius per label. -/
theorem roundedMoment_error {N : ℕ} (θ : ℕ → ℝ) {δ : ℝ}
    (hl : ∀ j < N, |θ j - (endpointIndex θ j : ℝ)*π| ≤ δ) :
    |(∑ j ∈ range N, (-1:ℝ)^j * cos (θ j)) -
      (∑ j ∈ range N, (-1:ℝ)^j * cos ((endpointIndex θ j : ℝ)*π))| ≤ N*δ := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range N, |(-1:ℝ)^j * cos (θ j) - (-1:ℝ)^j * cos ((endpointIndex θ j : ℝ)*π)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range N, δ := sum_le_sum (fun j hj => by
      rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact (abs_cos_sub_cos_le _ _).trans (hl _ (mem_range.mp hj)))
    _ = _ := by simp

end GaussianChains.JumpLocalization
