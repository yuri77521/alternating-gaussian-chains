import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GaussianChains.ClusterSeries

private theorem nonneg_of_deriv {f d : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ x, HasDerivAt f (d x) x) (hn : ∀ x : ℝ, 0 ≤ x → 0 ≤ d x)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).hasDerivWithinAt)
      (fun y hy => hn y (interior_subset hy))
  simpa [h0] using hm (Set.self_mem_Ici) hx hx

private theorem sin_lower : ∀ t : ℝ, 0 ≤ t → 0 ≤ Real.sin t - t + t ^ 3 / 6 := by
    apply nonneg_of_deriv (d := fun t => Real.cos t - 1 + t ^ 2 / 2)
    · norm_num
    · intro t
      convert ((Real.hasDerivAt_sin t).sub (hasDerivAt_id t)).add
        (((hasDerivAt_id t).pow 3).div_const 6) using 1
      simp
      ring
    · intro t _
      linarith [Real.one_sub_sq_div_two_le_cos (x := t)]

private theorem cos_upper : ∀ t : ℝ, 0 ≤ t → 0 ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    apply nonneg_of_deriv (d := fun t => Real.sin t - t + t ^ 3 / 6)
    · norm_num
    · intro t
      convert (((((hasDerivAt_id t).pow 2).div_const 2).const_sub 1).add
        (((hasDerivAt_id t).pow 4).div_const 24)).sub (Real.hasDerivAt_cos t) using 1
      simp
      ring
    · exact sin_lower

/-- Global cubic error for the linear sine approximation. -/
theorem sin_linear_bound (x : ℝ) : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
  suffices pos : ∀ y : ℝ, 0 ≤ y → |Real.sin y - y| ≤ |y| ^ 3 / 6 by
    rcases le_total 0 x with hx | hx
    · exact pos x hx
    · simpa only [Real.sin_neg, neg_sub_neg, abs_sub_comm x (Real.sin x), abs_neg] using pos (-x) (neg_nonneg.mpr hx)
  intro y hy
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.sin_le hy)), abs_of_nonneg hy]
  linarith [sin_lower y hy]

/-- Global quartic error for the quadratic cosine approximation. -/
theorem cos_second_bound (x : ℝ) :
    |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 / 24 := by
  suffices pos : ∀ y : ℝ, 0 ≤ y → |Real.cos y - (1 - y ^ 2 / 2)| ≤ y ^ 4 / 24 by
    rcases le_total 0 x with hx | hx
    · exact pos x hx
    · simpa only [Real.cos_neg, show (-x)^2 = x^2 by ring, show (-x)^4 = x^4 by ring, show (-x)^6 = x^6 by ring] using pos (-x) (neg_nonneg.mpr hx)
  intro y hy
  rw [abs_of_nonneg (sub_nonneg.mpr Real.one_sub_sq_div_two_le_cos)]
  linarith [cos_upper y hy]

/-- The degree-four cosine polynomial has a global, signed sixth-order
remainder. The inequalities follow by integrating alternating sine and
cosine polynomial bounds on the positive half-line. -/
theorem cos_fourth_bound (x : ℝ) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ (1 / 720 : ℝ) * x ^ 6 := by
  suffices pos : ∀ y : ℝ, 0 ≤ y →
      |Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24)| ≤ (1 / 720 : ℝ) * y ^ 6 by
    rcases le_total 0 x with hx | hx
    · exact pos x hx
    · simpa only [Real.cos_neg, show (-x)^2 = x^2 by ring, show (-x)^4 = x^4 by ring, show (-x)^6 = x^6 by ring] using pos (-x) (neg_nonneg.mpr hx)
  have h5 : ∀ t : ℝ, 0 ≤ t → 0 ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by
    apply nonneg_of_deriv (d := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
    · norm_num
    · intro t
      convert (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 6)).add
        (((hasDerivAt_id t).pow 5).div_const 120)).sub (Real.hasDerivAt_sin t) using 1
      simp
      ring
    · exact cos_upper
  have h6 : ∀ t : ℝ, 0 ≤ t → 0 ≤ Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720 := by
    apply nonneg_of_deriv (d := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
    · norm_num
    · intro t
      convert (((((Real.hasDerivAt_cos t).sub_const 1).add
        (((hasDerivAt_id t).pow 2).div_const 2)).sub
        (((hasDerivAt_id t).pow 4).div_const 24)).add
        (((hasDerivAt_id t).pow 6).div_const 720)) using 1
      simp
      ring
    · exact h5
  intro t ht
  rw [abs_of_nonpos (show Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24) ≤ 0 by linarith [cos_upper t ht])]
  linarith [h6 t ht]

end GaussianChains.ClusterSeries

