import ClustersWidth
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Derivative series of the normalized angular kernel in the locking proof. -/

noncomputable section
namespace GaussianChains
open Real

def angularWeight (p : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  ((k+2 : ℕ) : ℝ)^p * q^((k+2)^2-1)

def angularCos (p : ℕ) (q t : ℝ) : ℝ :=
  cos t + ∑' k : ℕ, angularWeight p q k * cos (((k+2 : ℕ) : ℝ)*t)

def angularSin (p : ℕ) (q t : ℝ) : ℝ :=
  sin t + ∑' k : ℕ, angularWeight p q k * sin (((k+2 : ℕ) : ℝ)*t)

abbrev angularK := angularCos 0

theorem angularK_eq (q t : ℝ) :
    angularK q t = cos t + ∑' k : ℕ, q^((k+2)^2-1) * cos (((k+2 : ℕ) : ℝ)*t) := by
  simp [angularK, angularCos, angularWeight]

@[simp] theorem angularSin_zero (p : ℕ) (q : ℝ) : angularSin p q 0 = 0 := by
  simp [angularSin]

@[simp] theorem angularSin_pi (p : ℕ) (q : ℝ) : angularSin p q π = 0 := by
  simp only [angularSin, sin_pi, Real.sin_nat_mul_pi, mul_zero, tsum_zero, add_zero]

theorem angularCos_even (p : ℕ) (q t : ℝ) :
    angularCos p q (-t) = angularCos p q t := by
  simp [angularCos, mul_neg]

theorem angularCos_pi_reflect (p : ℕ) (q t : ℝ) :
    angularCos p q (π - t) = angularCos p q (π + t) := by
  simp only [angularCos, mul_sub, mul_add, cos_sub, cos_add, sin_nat_mul_pi,
    sin_pi, zero_mul, add_zero, sub_zero]

private theorem norm_weighted_le {q : ℝ} (hq0 : 0 ≤ q) (p k : ℕ) {u : ℝ} (hu : |u| ≤ 1) :
    ‖angularWeight p q k * u‖ ≤ angularWeight p q k := by
  have hw : 0 ≤ angularWeight p q k := by unfold angularWeight; positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  simpa using mul_le_mul_of_nonneg_left hu hw

theorem angularCos_hasDerivAt {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (p : ℕ) (t : ℝ) :
    HasDerivAt (angularCos p q) (-angularSin (p+1) q t) t := by
  have hterm (k : ℕ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => angularWeight p q k * cos (((k+2 : ℕ) : ℝ)*y))
        (-(angularWeight (p+1) q k * sin (((k+2 : ℕ) : ℝ)*x))) x := by
    convert (((hasDerivAt_id x).const_mul ((k+2 : ℕ) : ℝ)).cos.const_mul
      (angularWeight p q k)) using 1
    simp [angularWeight, pow_succ]
    ring
  have hbound (k : ℕ) (x : ℝ) :
      ‖-(angularWeight (p+1) q k * sin (((k+2 : ℕ) : ℝ)*x))‖ ≤ angularWeight (p+1) q k :=
    (norm_neg _).le.trans (norm_weighted_le hq0 _ _ (abs_sin_le_one _))
  have h0 : Summable (fun k : ℕ => angularWeight p q k * cos (((k+2 : ℕ) : ℝ)*0)) :=
    Summable.of_norm_bounded (summable_widthMoment p hq0 hq1)
      (fun k => norm_weighted_le hq0 _ _ (abs_cos_le_one _))
  have htail := hasDerivAt_tsum (summable_widthMoment (p+1) hq0 hq1) hterm hbound h0 t
  have hv : -angularSin (p+1) q t = -sin t + ∑' k : ℕ,
      -(angularWeight (p+1) q k * sin (((k+2 : ℕ) : ℝ)*t)) := by
    rw [angularSin, tsum_neg]
    ring
  rw [hv]
  exact (Real.hasDerivAt_cos t).add htail

theorem angularSin_hasDerivAt {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (p : ℕ) (t : ℝ) :
    HasDerivAt (angularSin p q) (angularCos (p+1) q t) t := by
  have hterm (k : ℕ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => angularWeight p q k * sin (((k+2 : ℕ) : ℝ)*y))
        (angularWeight (p+1) q k * cos (((k+2 : ℕ) : ℝ)*x)) x := by
    convert (((hasDerivAt_id x).const_mul ((k+2 : ℕ) : ℝ)).sin.const_mul
      (angularWeight p q k)) using 1
    simp [angularWeight, pow_succ]
    ring
  have h0 : Summable (fun k : ℕ => angularWeight p q k * sin (((k+2 : ℕ) : ℝ)*0)) :=
    Summable.of_norm_bounded (summable_widthMoment p hq0 hq1)
      (fun k => norm_weighted_le hq0 _ _ (abs_sin_le_one _))
  have htail := hasDerivAt_tsum (summable_widthMoment (p+1) hq0 hq1) hterm
    (fun k x => norm_weighted_le hq0 _ _ (abs_cos_le_one _)) h0 t
  exact (Real.hasDerivAt_sin t).add htail

theorem deriv_angularCos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (p : ℕ) :
    deriv (angularCos p q) = -angularSin (p+1) q :=
  funext (fun x => (angularCos_hasDerivAt hq0 hq1 p x).deriv)

theorem deriv_angularSin {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (p : ℕ) :
    deriv (angularSin p q) = angularCos (p+1) q :=
  funext (fun x => (angularSin_hasDerivAt hq0 hq1 p x).deriv)

theorem angularMoments_contDiff {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n p : ℕ) :
    ContDiff ℝ n (angularCos p q) ∧ ContDiff ℝ n (angularSin p q) := by
  have hc (p : ℕ) : Differentiable ℝ (angularCos p q) :=
    fun x => (angularCos_hasDerivAt hq0 hq1 p x).differentiableAt
  have hs (p : ℕ) : Differentiable ℝ (angularSin p q) :=
    fun x => (angularSin_hasDerivAt hq0 hq1 p x).differentiableAt
  induction n generalizing p with
  | zero => simpa using And.intro (hc p).continuous (hs p).continuous
  | succ n ih =>
    simp only [Nat.cast_succ, contDiff_succ_iff_deriv, deriv_angularCos hq0 hq1,
      deriv_angularSin hq0 hq1]
    exact ⟨⟨hc p, by simp, (ih (p+1)).2.neg⟩, ⟨hs p, by simp, (ih (p+1)).1⟩⟩

theorem angularCos_tail_abs {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (p : ℕ) (t : ℝ) :
    |angularCos p q t - cos t| ≤ ∑' k, angularWeight p q k := by
  rw [angularCos, add_sub_cancel_left, ← Real.norm_eq_abs]
  apply tsum_of_norm_bounded (summable_widthMoment p hq0 hq1).hasSum
  exact fun k => norm_weighted_le hq0 _ _ (abs_cos_le_one _)

/-- These representatives are the second and fourth derivatives by the two
termwise differentiation theorems above. -/
theorem locking_curvature_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hR : widthR q ≤ 2/3)
    (t : ℝ) : |angularCos 2 q t| < 2 ∧ |angularCos 4 q t| < 2 ∧ 5/6 ≤ -angularCos 2 q π := by
  have h2 (x : ℝ) := (angularCos_tail_abs hq0 hq1 2 x).trans
    (secondMomentTail_le_quarter_R hq0 hq1)
  have h4 : |angularCos 4 q t - cos t| ≤ widthR q := angularCos_tail_abs hq0 hq1 4 t
  have hpi := (abs_le.mp (h2 π)).2
  rw [cos_pi] at hpi
  have hcos := abs_le.mp (abs_cos_le_one t)
  have hb2 := abs_le.mp (h2 t)
  have hb4 := abs_le.mp h4
  exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩,
    by linarith⟩

/-- The quadratic selection coefficient D = K''(π) − K''(0). -/
theorem locking_D_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hR : widthR q ≤ 2/3) :
    2 ≤ angularCos 2 q 0 - angularCos 2 q π ∧ angularCos 2 q 0 - angularCos 2 q π < 4 := by
  constructor
  · have hz : angularCos 2 q 0 = 1 + ∑' k, angularWeight 2 q k := by simp [angularCos]
    have hπ := (abs_le.mp (angularCos_tail_abs hq0 hq1 2 π)).2
    rw [cos_pi] at hπ
    linarith
  · have h0 := abs_lt.mp (locking_curvature_bounds hq0 hq1 hR 0).1
    have hπ := abs_lt.mp (locking_curvature_bounds hq0 hq1 hR π).1
    linarith

end GaussianChains
