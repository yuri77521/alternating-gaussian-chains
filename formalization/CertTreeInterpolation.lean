import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Error bounds for the spatial tables of Appendix A.  Both results use ordinary
derivatives on a closed real interval and apply to every point of a mesh cell. -/

namespace GaussianChains.Certificate
open Set

private lemma convex_tangent {D : Set ℝ} {g : ℝ → ℝ} {p a x : ℝ}
    (hc : ConvexOn ℝ D g) (ha : a ∈ D) (hx : x ∈ D) (hd : HasDerivAt g p a) :
    g a + p * (x - a) ≤ g x := by
  rcases lt_trichotomy a x with h | rfl | h
  · have hs := hc.le_slope_of_hasDerivAt ha hx h hd
    rw [slope_def_field] at hs
    linarith [(le_div_iff₀ (sub_pos.mpr h)).mp hs]
  · simp
  · have hs := hc.slope_le_of_hasDerivAt hx ha h hd
    rw [slope_def_field] at hs
    linarith [(div_le_iff₀ (sub_pos.mpr h)).mp hs]

/-- Lower Taylor parabola obtained from the convexity of a quadratic correction. -/
private lemma lower_taylor {D : Set ℝ} {f f' f'' : ℝ → ℝ} {M a x : ℝ}
    (hD : Convex ℝ D) (h₁ : ∀ t ∈ D, HasDerivAt f (f' t) t)
    (h₂ : ∀ t ∈ interior D, HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ interior D, -M ≤ f'' t) (ha : a ∈ D) (hx : x ∈ D) :
    -(M * (x - a)^2 / 2) ≤ f x - f a - f' a * (x - a) := by
  let g := fun t : ℝ => f t + (M / 2) * (t * t)
  let gp := fun t : ℝ => f' t + M * t
  have dg : ∀ t ∈ D, HasDerivAt g (gp t) t := by
    intro t ht
    convert (h₁ t ht).add (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (M / 2)) using 1
    simp [gp]
    ring
  have dgp : ∀ t ∈ interior D, HasDerivAt gp (f'' t + M) t := by
    intro t ht
    simpa [gp] using (h₂ t ht).add ((hasDerivAt_id t).const_mul M)
  have hc : ConvexOn ℝ D g := convexOn_of_hasDerivWithinAt2_nonneg hD
    (fun t ht => (dg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (dg t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => (dgp t ht).hasDerivWithinAt)
    (fun t ht => by linarith [hM t ht])
  have ht := convex_tangent hc ha hx (dg a ha)
  dsimp [g, gp] at ht
  linarith only [ht]

/-- The first-order Taylor error, with the sharp coefficient one half.
The expansion node may lie on either side of the query point. -/
theorem taylor_first_error {D : Set ℝ} {f f' f'' : ℝ → ℝ} {M a x : ℝ}
    (hD : Convex ℝ D) (h₁ : ∀ t ∈ D, HasDerivAt f (f' t) t)
    (h₂ : ∀ t ∈ interior D, HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ interior D, |f'' t| ≤ M) (ha : a ∈ D) (hx : x ∈ D) :
    |f x - f a - f' a * (x - a)| ≤ M * (x - a)^2 / 2 := by
  refine abs_le.mpr ⟨lower_taylor hD h₁ h₂ (fun t ht => (abs_le.mp (hM t ht)).1) ha hx, ?_⟩
  have upper := lower_taylor (f := fun t => -f t) (f' := fun t => -f' t)
    (f'' := fun t => -f'' t) hD (fun t ht => (h₁ t ht).neg) (fun t ht => (h₂ t ht).neg)
    (fun t ht => neg_le_neg (abs_le.mp (hM t ht)).2) ha hx
  dsimp at upper
  linarith only [upper]

/-- Absolute difference from the line joining two neighboring node values.
The bound applies to the closed mesh cell, including both endpoints. -/
theorem interpolation_error {f f' f'' : ℝ → ℝ} {a b x M : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) (hM₀ : 0 ≤ M)
    (h₁ : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (h₂ : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ interior (Icc a b), |f'' t| ≤ M) :
    |((b - x) * f a + (x - a) * f b) / (b - a) - f x| ≤ M * (b - a)^2 / 8 := by
  have A := abs_le.mp (taylor_first_error (convex_Icc a b) h₁ h₂ hM hx (left_mem_Icc.mpr hab.le))
  have B := abs_le.mp (taylor_first_error (convex_Icc a b) h₁ h₂ hM hx (right_mem_Icc.mpr hab.le))
  have hleft := sub_nonneg.mpr hx.1
  have hright := sub_nonneg.mpr hx.2
  have hspan := sub_pos.mpr hab
  have hbudget : M * (x - a) * (b - x) / 2 ≤ M * (b - a)^2 / 8 := by
    nlinarith only [mul_nonneg hM₀ (sq_nonneg (2*x-a-b))]
  refine le_trans (abs_le.mpr ⟨?_, ?_⟩) hbudget
  · rw [le_sub_iff_add_le, le_div_iff₀ hspan]
    nlinarith only [mul_le_mul_of_nonneg_left A.1 hright, mul_le_mul_of_nonneg_left B.1 hleft]
  · rw [sub_le_iff_le_add, div_le_iff₀ hspan]
    nlinarith only [mul_le_mul_of_nonneg_left A.2 hright, mul_le_mul_of_nonneg_left B.2 hleft]

/-- Taking the hull of uncertain endpoint values, then widening by the
interpolation budget, encloses the function on the entire mesh cell. -/
theorem interpolation_enclosure {f f' f'' : ℝ → ℝ} {a b x M lo hi : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) (hM₀ : 0 ≤ M)
    (h₁ : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (h₂ : ∀ t ∈ interior (Icc a b), HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ interior (Icc a b), |f'' t| ≤ M)
    (ha : f a ∈ Icc lo hi) (hb : f b ∈ Icc lo hi) :
    f x ∈ Icc (lo - M * (b-a)^2 / 8) (hi + M * (b-a)^2 / 8) := by
  have he := abs_le.mp (interpolation_error hab hx hM₀ h₁ h₂ hM)
  have hl : lo ≤ ((b-x)*f a + (x-a)*f b)/(b-a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ha.1 (sub_nonneg.mpr hx.2),
      mul_le_mul_of_nonneg_left hb.1 (sub_nonneg.mpr hx.1)]
  have hh : ((b-x)*f a + (x-a)*f b)/(b-a) ≤ hi := by
    apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr hx.2),
      mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr hx.1)]
  exact ⟨by linarith only [hl, he.2], by linarith only [hh, he.1]⟩

/-- Add the uncertainties in the sampled value and slope to the analytic Taylor
remainder.  The slope uncertainty is scaled by the distance to the node. -/
theorem taylor_sample_error {D : Set ℝ} {f f' f'' : ℝ → ℝ} {M a x v p ev ep : ℝ}
    (hD : Convex ℝ D) (h₁ : ∀ t ∈ D, HasDerivAt f (f' t) t)
    (h₂ : ∀ t ∈ interior D, HasDerivAt f' (f'' t) t)
    (hM : ∀ t ∈ interior D, |f'' t| ≤ M) (ha : a ∈ D) (hx : x ∈ D)
    (hv : |f a - v| ≤ ev) (hp : |f' a - p| ≤ ep) :
    |f x - (v + p * (x - a))| ≤ M * (x - a)^2 / 2 + ev + ep * |x - a| := by
  let R := f x - f a - f' a * (x - a)
  have hR : |R| ≤ M * (x - a)^2 / 2 := taylor_first_error hD h₁ h₂ hM ha hx
  have iden : f x - (v + p * (x - a)) = R + (f a - v) + (f' a - p) * (x - a) := by
    dsimp [R]
    ring
  rw [iden]
  calc
    _ ≤ |R + (f a - v)| + |(f' a - p) * (x - a)| := abs_add_le _ _
    _ ≤ (|R| + |f a - v|) + |f' a - p| * |x - a| := by
      rw [abs_mul]
      exact add_le_add (abs_add_le R (f a - v)) le_rfl
    _ ≤ _ := add_le_add (add_le_add hR hv) (mul_le_mul_of_nonneg_right hp (abs_nonneg _))

end GaussianChains.Certificate
