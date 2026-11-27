import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Local four-center curvature argument for the width-22 theorem. -/

namespace GaussianChains.Point22

open Set

abbrev Point := ℝ × ℝ × ℝ

/-- Consecutive distances from the fixed origin, including the closing arc. -/
def side (p : Point) : Fin 4 → ℝ
  | 0 => p.1
  | 1 => p.2.1 - p.1
  | 2 => p.2.2 - p.2.1
  | 3 => 1 - p.2.2

def localDomain : Set Point := {p | ∀ i, side p i ∈ Icc (21/100) (31/100)}

theorem convex_localDomain : Convex ℝ localDomain := by
  intro x hx y hy a b ha hb hab i
  have he : side (a • x + b • y) i = a * side x i + b * side y i := by
    fin_cases i <;> simp [side, smul_eq_mul] <;> linarith
  rw [he]
  exact (convex_Icc (21/100 : ℝ) (31/100)) (hx i) (hy i) ha hb hab

/-- Variable part of the unordered signed pair score after packing the triple. -/
def variableScore (G C : ℝ → ℝ) (p : Point) : ℝ :=
  -C p.1 + C p.2.1 - C p.2.2 - G (p.2.1-p.1) + G (p.2.2-p.1) - G (p.2.2-p.2.1)

def sideSquares (r z t : ℝ) : ℝ := r^2 + (z-r)^2 + (t-z)^2 + t^2

theorem sideSquares_sub_diagonals (r z t : ℝ) :
    sideSquares r z t - (z^2 + (t-r)^2) = (r+t-z)^2 := by
  unfold sideSquares
  ring

theorem sideSquares_pos {r z t : ℝ} (h : (r,z,t) ≠ (0,0,0)) : 0 < sideSquares r z t := by
  by_contra! hc
  unfold sideSquares at hc
  have hr : r = 0 := by
    apply sq_eq_zero_iff.mp
    nlinarith only [hc, sq_nonneg r, sq_nonneg (z-r), sq_nonneg (t-z), sq_nonneg t]
  have ht : t = 0 := by
    apply sq_eq_zero_iff.mp
    nlinarith only [hc, sq_nonneg r, sq_nonneg (z-r), sq_nonneg (t-z), sq_nonneg t]
  subst r
  subst t
  have hz : z = 0 := by
    apply sq_eq_zero_iff.mp
    nlinarith only [hc, sq_nonneg z]
  exact h (by simp [hz])

/-- The six pointwise estimates on the second derivatives used by the Hessian test. -/
structure KernelBoundsAt (G₂ C₂ : ℝ → ℝ) (p : Point) : Prop where
  origin_right : 14 ≤ C₂ p.1
  origin_left : 14 ≤ C₂ p.2.2
  right_side : 14 ≤ G₂ (p.2.1-p.1)
  left_side : 14 ≤ G₂ (p.2.2-p.2.1)
  origin_diagonal : C₂ p.2.1 ≤ 7
  cross_diagonal : G₂ (p.2.2-p.1) ≤ 7

/-- Real interval statements needed to instantiate the curvature test. Diagonals are
controlled from both complementary arcs, including at the endpoints. -/
theorem kernelBoundsAt_of_intervals {G₂ C₂ : ℝ → ℝ} {p : Point} (hp : p ∈ localDomain)
    (hsideG : ∀ x ∈ Icc (21/100 : ℝ) (31/100), 14 ≤ G₂ x)
    (hsideC : ∀ x ∈ Icc (21/100 : ℝ) (31/100), 14 ≤ C₂ x)
    (hdiagG : ∀ x ∈ Icc (42/100 : ℝ) (58/100), G₂ x ≤ 7)
    (hdiagC : ∀ x ∈ Icc (42/100 : ℝ) (58/100), C₂ x ≤ 7)
    (hreflect : ∀ x, C₂ (1-x) = C₂ x) : KernelBoundsAt G₂ C₂ p := by
  have h₀ := hp 0
  have h₁ := hp 1
  have h₂ := hp 2
  have h₃ := hp 3
  change p.1 ∈ Icc _ _ at h₀
  change p.2.1 - p.1 ∈ Icc _ _ at h₁
  change p.2.2 - p.2.1 ∈ Icc _ _ at h₂
  change 1-p.2.2 ∈ Icc _ _ at h₃
  refine ⟨hsideC _ h₀, (hreflect p.2.2) ▸ hsideC _ h₃, hsideG _ h₁, hsideG _ h₂,
    hdiagC _ ⟨?_, ?_⟩, hdiagG _ ⟨?_, ?_⟩⟩ <;>
    linarith only [h₀.1, h₁.1, h₂.1, h₃.1]

def curvature (G₂ C₂ : ℝ → ℝ) (p v : Point) : ℝ :=
  -C₂ p.1 * v.1^2 + C₂ p.2.1 * v.2.1^2 - C₂ p.2.2 * v.2.2^2 -
    G₂ (p.2.1-p.1) * (v.2.1-v.1)^2 + G₂ (p.2.2-p.1) * (v.2.2-v.1)^2 -
    G₂ (p.2.2-p.2.1) * (v.2.2-v.2.1)^2

theorem curvature_le {G₂ C₂ : ℝ → ℝ} {p : Point} (hc : KernelBoundsAt G₂ C₂ p) (v : Point) :
    curvature G₂ C₂ p v ≤ -7 * sideSquares v.1 v.2.1 v.2.2 := by
  have hsd := sideSquares_sub_diagonals v.1 v.2.1 v.2.2
  unfold curvature sideSquares at *
  linarith [mul_le_mul_of_nonneg_right hc.origin_right (sq_nonneg v.1),
    mul_le_mul_of_nonneg_right hc.origin_left (sq_nonneg v.2.2),
    mul_le_mul_of_nonneg_right hc.right_side (sq_nonneg (v.2.1-v.1)),
    mul_le_mul_of_nonneg_right hc.left_side (sq_nonneg (v.2.2-v.2.1)),
    mul_le_mul_of_nonneg_right hc.origin_diagonal (sq_nonneg v.2.1),
    mul_le_mul_of_nonneg_right hc.cross_diagonal (sq_nonneg (v.2.2-v.1)),
    sq_nonneg (v.1+v.2.2-v.2.1)]

theorem curvature_neg_of_ne_zero {G₂ C₂ : ℝ → ℝ} {p v : Point}
    (hc : KernelBoundsAt G₂ C₂ p) (hv : v ≠ 0) : curvature G₂ C₂ p v < 0 := by
  exact (curvature_le hc v).trans_lt (mul_neg_of_neg_of_pos (by norm_num) (sideSquares_pos hv))

/-- The six oriented pair differences in the reduced score. -/
private def argument (p : Point) : Fin 6 → ℝ
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2
  | 3 => p.2.1 - p.1
  | 4 => p.2.2 - p.1
  | 5 => p.2.2 - p.2.1

private def term (G C : ℝ → ℝ) : Fin 6 → ℝ → ℝ
  | 0 => fun x => -C x
  | 1 => C
  | 2 => fun x => -C x
  | 3 => fun x => -G x
  | 4 => G
  | 5 => fun x => -G x

private theorem score_eq_sum (G C : ℝ → ℝ) (p : Point) :
    variableScore G C p = ∑ i, term G C i (argument p i) := by
  simp [variableScore, Fin.sum_univ_succ, term, argument]
  ring

private theorem curvature_eq_sum (G₂ C₂ : ℝ → ℝ) (p v : Point) :
    curvature G₂ C₂ p v = ∑ i, term G₂ C₂ i (argument p i) * argument v i ^ 2 := by
  simp [curvature, Fin.sum_univ_succ, term, argument]
  ring

private theorem arg_line (p v : Point) (u : ℝ) (i : Fin 6) :
    argument (p + u • v) i = argument p i + u * argument v i := by
  fin_cases i <;> simp [argument, smul_eq_mul] <;> ring

private theorem term_hasDerivAt {G C G₁ C₁ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (G₁ u) u) (hC : ∀ u, HasDerivAt C (C₁ u) u)
    (i : Fin 6) (x : ℝ) :
    HasDerivAt (term G C i) (term G₁ C₁ i x) x := by
  fin_cases i <;> first | exact (hC x).neg | exact (hG x).neg | exact hC x | exact hG x

private theorem term_line_hasDerivAt {G C G₁ C₁ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (G₁ u) u) (hC : ∀ u, HasDerivAt C (C₁ u) u)
    (p v : Point) (u : ℝ) (i : Fin 6) :
    HasDerivAt (fun w => term G C i (argument (p + w • v) i))
      (term G₁ C₁ i (argument (p + u • v) i) * argument v i) u := by
  simp_rw [arg_line]
  have hlin : HasDerivAt (fun w : ℝ => argument p i + w * argument v i) (argument v i) u := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul] using
      (hasDerivAt_const u (argument p i)).add ((hasDerivAt_id u).mul_const (argument v i))
  exact (term_hasDerivAt hG hC i _).comp u hlin

/-- First directional derivative of the score when the translation gauge is fixed. -/
def slope (G₁ C₁ : ℝ → ℝ) (p v : Point) : ℝ :=
  ∑ i, term G₁ C₁ i (argument p i) * argument v i

theorem variableScore_line_hasDerivAt {G C G₁ C₁ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (G₁ u) u) (hC : ∀ u, HasDerivAt C (C₁ u) u)
    (p v : Point) (u : ℝ) :
    HasDerivAt (fun w => variableScore G C (p + w • v)) (slope G₁ C₁ (p + u • v) v) u := by
  simp_rw [score_eq_sum]
  exact HasDerivAt.fun_sum fun i _ => term_line_hasDerivAt hG hC p v u i

theorem slope_line_hasDerivAt {G₁ C₁ G₂ C₂ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G₁ (G₂ u) u) (hC : ∀ u, HasDerivAt C₁ (C₂ u) u)
    (p v : Point) (u : ℝ) :
    HasDerivAt (fun w => slope G₁ C₁ (p + w • v) v) (curvature G₂ C₂ (p + u • v) v) u := by
  rw [curvature_eq_sum]
  unfold slope
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [mul_assoc, pow_two] using (term_line_hasDerivAt hG hC p v u i).mul_const (argument v i)

private theorem line_convex_mixture (x y : Point) (a b : ℝ) (hab : a+b=1) :
    x + b • (y-x) = a • x + b • y := by
  calc
    x + b • (y-x) = (a+b) • x + b • (y-x) := by rw [hab, one_smul]
    _ = _ := by rw [add_smul, smul_sub]; abel

private theorem strictConcaveOn_score_segment {G C G₁ C₁ G₂ C₂ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (G₁ u) u) (hC : ∀ u, HasDerivAt C (C₁ u) u)
    (hG₂ : ∀ u, HasDerivAt G₁ (G₂ u) u) (hC₂ : ∀ u, HasDerivAt C₁ (C₂ u) u)
    (hbounds : ∀ p ∈ localDomain, KernelBoundsAt G₂ C₂ p)
    {x y : Point} (hx : x ∈ localDomain) (hy : y ∈ localDomain) (hxy : x ≠ y) :
    StrictConcaveOn ℝ (Icc 0 1) (fun u : ℝ => variableScore G C (x + u • (y-x))) := by
  let v := y - x
  let f := fun u : ℝ => variableScore G C (x + u • v)
  have hd (u : ℝ) : HasDerivAt f (slope G₁ C₁ (x + u • v) v) u :=
    variableScore_line_hasDerivAt hG hC x v u
  have he : deriv f = fun u => slope G₁ C₁ (x + u • v) v :=
    funext fun u => (hd u).deriv
  have hn : v ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hconc : StrictConcaveOn ℝ (Icc 0 1) f := by
    apply strictConcaveOn_of_deriv2_neg' (convex_Icc _ _) (continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)).continuousOn
    intro u hu
    change deriv (deriv f) u < 0
    rw [he, (slope_line_hasDerivAt hG₂ hC₂ x v u).deriv]
    apply curvature_neg_of_ne_zero _ hn
    apply hbounds
    change x + u • (y-x) ∈ localDomain
    rw [line_convex_mixture x y (1-u) u (by ring)]
    exact convex_localDomain hx hy (sub_nonneg.mpr hu.2) hu.1 (by ring)
  exact hconc

theorem variableScore_strictConcaveOn {G C G₁ C₁ G₂ C₂ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (G₁ u) u) (hC : ∀ u, HasDerivAt C (C₁ u) u)
    (hG₂ : ∀ u, HasDerivAt G₁ (G₂ u) u) (hC₂ : ∀ u, HasDerivAt C₁ (C₂ u) u)
    (hbounds : ∀ p ∈ localDomain, KernelBoundsAt G₂ C₂ p) :
    StrictConcaveOn ℝ localDomain (variableScore G C) := by
  refine ⟨convex_localDomain, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hconc := strictConcaveOn_score_segment hG hC hG₂ hC₂ hbounds hx hy hxy
  have h := hconc.2 (show (0:ℝ) ∈ Icc 0 1 by simp) (show (1:ℝ) ∈ Icc 0 1 by simp)
    zero_ne_one ha hb hab
  have h1 : x + (y-x) = y := by abel
  simpa [smul_eq_mul, h1, line_convex_mixture x y a b hab] using h

/-- A stationary point dominates every other point of the closed local domain,
including its boundary. This needs no interior assumption at the stationary point. -/
theorem stationary_score_strict_max {G C G₁ C₁ G₂ C₂ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (G₁ u) u) (hC : ∀ u, HasDerivAt C (C₁ u) u)
    (hG₂ : ∀ u, HasDerivAt G₁ (G₂ u) u) (hC₂ : ∀ u, HasDerivAt C₁ (C₂ u) u)
    (hbounds : ∀ p ∈ localDomain, KernelBoundsAt G₂ C₂ p)
    {x y : Point} (hx : x ∈ localDomain) (hy : y ∈ localDomain) (hxy : x ≠ y)
    (hcrit : ∀ v : Point, slope G₁ C₁ x v = 0) : variableScore G C y < variableScore G C x := by
  have hconc := strictConcaveOn_score_segment hG hC hG₂ hC₂ hbounds hx hy hxy
  have hd := variableScore_line_hasDerivAt hG hC x (y-x) 0
  have hlt := hconc.slope_lt_of_hasDerivAt (show (0:ℝ) ∈ Icc 0 1 by simp)
    (show (1:ℝ) ∈ Icc 0 1 by simp) zero_lt_one hd
  have h1 : x+(y-x)=y := by abel
  simpa [slope_def_field, h1, hcrit, sub_lt_zero] using hlt

theorem local_maximizer_unique {G C G₁ C₁ G₂ C₂ : ℝ → ℝ}
    (hG : ∀ u, HasDerivAt G (G₁ u) u) (hC : ∀ u, HasDerivAt C (C₁ u) u)
    (hG₂ : ∀ u, HasDerivAt G₁ (G₂ u) u) (hC₂ : ∀ u, HasDerivAt C₁ (C₂ u) u)
    (hbounds : ∀ p ∈ localDomain, KernelBoundsAt G₂ C₂ p)
    {x y : Point} (hx : x ∈ localDomain) (hy : y ∈ localDomain)
    (hxmax : IsMaxOn (variableScore G C) localDomain x)
    (hymax : IsMaxOn (variableScore G C) localDomain y) : x = y :=
  (variableScore_strictConcaveOn hG hC hG₂ hC₂ hbounds).eq_of_isMaxOn hxmax hymax hx hy

/-- Differentiating reflection about the half-period makes the first derivative odd. -/
theorem derivative_reflection {F F₁ : ℝ → ℝ} (hd : ∀ u, HasDerivAt F (F₁ u) u)
    (href : ∀ x, F (1-x) = F x) (x : ℝ) : F₁ (1-x) = -F₁ x := by
  have ha : HasDerivAt (fun y : ℝ => 1-y) (-1) x := by
    simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
  have H := (hd (1-x)).comp x ha
  change HasDerivAt (fun y => F (1-y)) _ x at H
  simp_rw [href] at H
  have ht := H.unique (hd x)
  linarith

/-- On the reflection-fixed line, the derivative in every spatial direction is the
one scalar residual from the force equation times the antisymmetric velocity. -/
theorem slope_on_reflection_line {G₁ C₁ : ℝ → ℝ}
    (hG : ∀ x, G₁ (1-x) = -G₁ x) (hC : ∀ x, C₁ (1-x) = -C₁ x)
    (R : ℝ) (v : Point) :
    slope G₁ C₁ (R,1/2,1-R) v =
      (v.2.2-v.1) * (C₁ R - G₁ (1/2-R) - G₁ (2*R)) := by
  have hh := hC (1/2)
  have hmid : C₁ (1/2) = 0 := by norm_num at hh; linarith
  have ht : 1-R-R=1-2*R := by ring
  simp [slope, Fin.sum_univ_succ, argument, term, ht, hC R, hG (2*R)]
  ring_nf at hmid ⊢
  rw [hmid]
  ring

theorem fixed_line_force_iff {G₁ C₁ : ℝ → ℝ}
    (hG : ∀ x, G₁ (1-x) = -G₁ x) (hC : ∀ x, C₁ (1-x) = -C₁ x) (R : ℝ) :
    (∀ v, slope G₁ C₁ (R,1/2,1-R) v = 0) ↔ C₁ R - G₁ (1/2-R) - G₁ (2*R) = 0 := by
  constructor
  · intro h
    simpa only [slope_on_reflection_line hG hC, sub_zero, one_mul] using h (0,0,1)
  · intro h v
    rw [slope_on_reflection_line hG hC, h, mul_zero]

end GaussianChains.Point22
