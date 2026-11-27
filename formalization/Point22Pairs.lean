import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Analytic estimates for removing adjacent opposite-charge pairs (Table 3).
Distances are real lifts on one residual arc. -/

namespace GaussianChains.Point22

open Set

private theorem diff_bound {f d : ℝ → ℝ} {a b C : ℝ}
    (hd : ∀ x, HasDerivAt f (d x) x) (hab : a ≤ b)
    (hle : ∀ x ∈ Ioo a b, d x ≤ C) : f b - f a ≤ C*(b-a) := by
  rcases hab.eq_or_lt with rfl | h
  · simp
  obtain ⟨x,hx,hs⟩ := exists_hasDerivAt_eq_slope f d h
    ((continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt).continuousOn) (fun x _ => hd x)
  have hb := hle x hx
  rw [hs, div_le_iff₀ (sub_pos.mpr h)] at hb
  exact hb

/-- The derivative of the field of the two residual opposite particles is
bounded above by the arc imbalance, even on the longer arc. At most one
distance can exceed the half-period. -/
theorem residual_field_slope_le {D : ℝ → ℝ} {K δ u x : ℝ}
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hu : u ≤ 1) (hu' : u ≤ 1/2+δ)
    (hx : 0 ≤ x) (hxu : x ≤ u) (half : D (1/2) = 0)
    (negative : ∀ t ∈ Icc (0:ℝ) (1/2), D t ≤ 0)
    (lip : ∀ x y, |D x-D y| ≤ K*|x-y|) : D x + D (u-x) ≤ K*δ := by
  have bound (t : ℝ) (ht : 1/2 ≤ t) (htu : t ≤ u) : D t ≤ K*δ := by
    have hb := lip t (1/2)
    rw [half, sub_zero, abs_of_nonneg (sub_nonneg.mpr ht)] at hb
    exact (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left (by linarith) hK))
  by_cases h : 1/2 ≤ x
  · linarith [bound x h hxu, negative (u-x) ⟨by linarith, by linarith⟩]
  by_cases h' : 1/2 ≤ u-x
  · linarith [negative x ⟨hx,by linarith⟩, bound (u-x) h' (by linarith)]
  linarith [negative x ⟨hx,by linarith⟩, negative (u-x) ⟨by linarith,by linarith⟩,
    mul_nonneg hK hδ]

theorem residual_pair_first_difference {G D : ℝ → ℝ} {K δ u v h : ℝ}
    (hd : ∀ x, HasDerivAt G (D x) x) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hu : u ≤ 1) (hu' : u ≤ 1/2+δ) (hv : 0 ≤ v) (hh : 0 ≤ h) (hvu : v+h ≤ u)
    (half : D (1/2) = 0) (negative : ∀ t ∈ Icc (0:ℝ) (1/2), D t ≤ 0)
    (lip : ∀ x y, |D x-D y| ≤ K*|x-y|) :
    (G (v+h) - G v) + (G (u-v) - G (u-(v+h))) ≤ K*δ*h := by
  let f (x : ℝ) := G x - G (u-x)
  have hder (x : ℝ) : HasDerivAt f (D x+D (u-x)) x := by
    convert (hd x).sub ((hd (u-x)).comp x ((hasDerivAt_id x).const_sub u)) using 1 <;>
      dsimp [f, Function.comp_def] <;> ring
  have hh' : v ≤ v+h := by linarith
  have hb := diff_bound hder hh' (C := K*δ) fun x hx =>
    residual_field_slope_le hK hδ hu hu' (by linarith [hx.1]) (by linarith [hx.2])
      half negative lip
  dsimp [f] at hb
  linarith

/-- Each removed opposite pair contributes at most K h² to the ordered
self score, including both labels. -/
theorem opposite_pair_self_score {G D : ℝ → ℝ} {K h : ℝ}
    (hd : ∀ x, HasDerivAt G (D x) x) (h0 : D 0 = 0) (hh : 0 ≤ h)
    (lip : ∀ x y, |D x-D y| ≤ K*|x-y|) :
    2*(G 0-G h) ≤ K*h^2 := by
  let f (x : ℝ) := -G x - K*x^2/2
  have hder (x : ℝ) : HasDerivAt f (-D x - K*x) x := by
    convert (hd x).neg.sub ((((hasDerivAt_id x).pow 2).const_mul K).div_const 2)
      using 1 <;> dsimp [f] <;> ring
  have hb := diff_bound hder hh (C := 0) fun x hx => by
    have hm := lip x 0
    rw [h0, sub_zero, sub_zero, abs_of_pos hx.1] at hm
    linarith [(abs_le.mp hm).1]
  dsimp [f] at hb
  linarith

/-- Mixed finite difference for two contacting dipoles, before multiplication
by their relative sign. -/
theorem dipole_mixed_difference {G D : ℝ → ℝ} {K h a : ℝ}
    (hd : ∀ x, HasDerivAt G (D x) x) (hh : 0 ≤ h)
    (lip : ∀ x y, |D x-D y| ≤ K*|x-y|) :
    |(G (a+h+h)-G (a+h))-(G (a+h)-G a)| ≤ K*h^2 := by
  let f (x : ℝ) := G (x+h) - G x
  have hD (x : ℝ) : HasDerivAt f (D (x+h)-D x) x := by
    simpa [f, Function.comp_def] using
      (((hd (x+h)).comp x ((hasDerivAt_id x).add_const h)).sub (hd x))
  have slope (x : ℝ) : |D (x+h)-D x| ≤ K*h := by
    simpa [abs_of_nonneg hh] using lip (x+h) x
  have hp := diff_bound hD (show a ≤ a+h by linarith) (C := K*h) fun x _ =>
    (abs_le.mp (slope x)).2
  have hn := diff_bound (fun x => (hD x).neg) (show a ≤ a+h by linarith)
    (C := K*h) fun x _ => neg_le.mp (abs_le.mp (slope x)).1
  dsimp [f] at hp hn
  rw [abs_le]
  constructor <;> nlinarith

end GaussianChains.Point22
