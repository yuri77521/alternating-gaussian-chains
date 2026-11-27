import PackedFaceBoundsComplexBridge
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace GaussianChains.PackedFace
open Polynomial Polynomial.Chebyshev Set
noncomputable section

/-- Along any holomorphic family contained in the polydisc the *actual*
series for the slope is analytic, with the same summable majorant. -/
theorem analyticOnNhd_complexSlope_along {D : Set ℂ} (hD : IsOpen D)
    {q x z : ℂ → ℂ} (hq : DifferentiableOn ℂ q D) (hx : DifferentiableOn ℂ x D)
    (hz : DifferentiableOn ℂ z D)
    (hb : ∀ w ∈ D, ‖q w‖ ≤ 1/2 ∧ ‖x w‖ ≤ 2 ∧ ‖z w‖ ≤ 2) :
    AnalyticOnNhd ℂ (fun w => ∑' k : ℕ, complexSlopeMode (k+1) (q w) (x w) (z w)) D := by
  apply DifferentiableOn.analyticOnNhd _ hD
  apply Complex.differentiableOn_tsum_of_summable_norm ((summable_nat_add_iff 1).mpr summable_slopeMajorant)
  · intro k
    unfold complexSlopeMode
    fun_prop
  · exact hD
  · intro k w hw
    exact norm_complexSlopeMode_le (k+1) (hb w hw).1 (hb w hw).2.1 (hb w hw).2.2

/-- Restrict a complex analytic slice to the real axis and identify its
sum term by term with the endpoint slope in equation (10). -/
theorem analyticAt_endpointSlope_along {Q X Z : ℂ → ℂ} {q x z : ℝ → ℝ} {t : ℝ}
    (hQ : Differentiable ℂ Q) (hX : Differentiable ℂ X) (hZ : Differentiable ℂ Z)
    (hrQ : ∀ a : ℝ, Q a = (q a : ℂ)) (hrX : ∀ a : ℝ, X a = (x a : ℂ))
    (hrZ : ∀ a : ℝ, Z a = (z a : ℂ))
    (hq : |q t| < 1/2) (hx : |x t| < 2) (hz : |z t| < 2) :
    AnalyticAt ℝ (fun a => endpointSlope (q a) (x a) (z a)) t := by
  let D : Set ℂ := {w | ‖Q w‖ < 1/2} ∩ {w | ‖X w‖ < 2} ∩ {w | ‖Z w‖ < 2}
  have hD : IsOpen D := ((isOpen_lt hQ.continuous.norm continuous_const).inter
    (isOpen_lt hX.continuous.norm continuous_const)).inter
    (isOpen_lt hZ.continuous.norm continuous_const)
  have ht : (t : ℂ) ∈ D := by
    change (‖Q (t:ℂ)‖ < 1/2 ∧ ‖X (t:ℂ)‖ < 2) ∧ ‖Z (t:ℂ)‖ < 2
    simpa only [hrQ, hrX, hrZ, Complex.norm_real, Real.norm_eq_abs] using And.intro (And.intro hq hx) hz
  have he := analyticOnNhd_complexSlope_along hD hQ.differentiableOn hX.differentiableOn
    hZ.differentiableOn (fun _ h => ⟨h.1.1.le,h.1.2.le,h.2.le⟩) _ ht
  have hreal : AnalyticAt ℝ (fun a : ℝ =>
      (∑' k : ℕ, complexSlopeMode (k+1) (Q a) (X a) (Z a)).re) t :=
    (Complex.reCLM.analyticAt _).comp (he.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))
  convert hreal using 1
  funext a
  simp only [hrQ, hrX, hrZ, ← ofReal_endpointSlope, Complex.ofReal_re]

/-- Analyticity in the nome with the two endpoint abscissas fixed. -/
theorem analyticAt_endpointSlope_q {q x z : ℝ} (hq : |q| < 1/2)
    (hx : |x| < 2) (hz : |z| < 2) :
    AnalyticAt ℝ (fun a => endpointSlope a x z) q := by
  apply analyticAt_endpointSlope_along (Q := id) (X := fun _ => (x : ℂ)) (Z := fun _ => (z : ℂ))
    (q := id) (x := fun _ => x) (z := fun _ => z) <;> first | assumption | fun_prop | intros; rfl

/-- Analyticity in the abscissa along the *moving* outer-contact endpoint. -/
theorem analyticAt_outerSlope_x {q x : ℝ} (hq : |q| < 1/2)
    (hx : |x| < 2) (hz : |3*x-4*x^3| < 2) :
    AnalyticAt ℝ (fun a => endpointSlope q a (3*a-4*a^3)) x := by
  apply analyticAt_endpointSlope_along (Q := fun _ => (q : ℂ)) (X := id)
    (Z := fun a => 3*a-4*a^3) (q := fun _ => q) (x := id) (z := fun a => 3*a-4*a^3)
  all_goals first | assumption | fun_prop | intros; push_cast; rfl

/-- On the outer physical endpoint both arguments are cosines. Consequently
the analytic extension covers the endpoint even when the displacement vanishes. -/
theorem analyticAt_contactSlope_h {q : ℝ} (hq : |q| < 1/2) (h : ℝ) :
    AnalyticAt ℝ (fun a => endpointSlope q (Real.cos (2*Real.pi*a))
      (Real.cos (2*Real.pi*(1/2-3*a)))) h := by
  apply analyticAt_endpointSlope_along (Q := fun _ => (q : ℂ))
    (X := fun a => Complex.cos (2*(Real.pi:ℂ)*a))
    (Z := fun a => Complex.cos (2*(Real.pi:ℂ)*(1/2-3*a)))
    (q := fun _ => q) (x := fun a => Real.cos (2*Real.pi*a))
    (z := fun a => Real.cos (2*Real.pi*(1/2-3*a)))
  · fun_prop
  · fun_prop
  · fun_prop
  · intro a; rfl
  · intro a; simp
  · intro a; simp
  · exact hq
  · exact (Real.abs_cos_le_one _).trans_lt (by norm_num : (1:ℝ) < 2)
  · exact (Real.abs_cos_le_one _).trans_lt (by norm_num : (1:ℝ) < 2)

end
end GaussianChains.PackedFace
