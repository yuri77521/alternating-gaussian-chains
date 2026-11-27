import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! Real-variable part of the two endpoint tests for Theorem 3. -/
noncomputable section

namespace GaussianChains.PackedFace
open Set

/-- The sign change is in the open transition interval. Both endpoints are
included in the uniqueness assertion and the zero has nonzero derivative. -/
theorem endpoint_root_of_deriv_neg (P : ℝ → ℝ)
    (hc : ContinuousOn P (Icc (1/8) (1/6)))
    (hd : ∀ h ∈ Ioo (1/8) (1/6), deriv P h < 0)
    (hl : 0 < P (1/8)) (hr : P (1/6) < 0) :
    ∃ r ∈ Ioo (1/8) (1/6), P r = 0 ∧ deriv P r ≠ 0 ∧
      ∀ h ∈ Icc (1/8) (1/6), P h = 0 ↔ h = r := by
  have ha : StrictAntiOn P (Icc (1/8) (1/6)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hc (by simpa only [interior_Icc] using hd)
  obtain ⟨r, hri, he⟩ := intermediate_value_Ioo' (by norm_num : (1/8 : ℝ) ≤ 1/6) hc ⟨hr, hl⟩
  refine ⟨r, hri, he, (hd r hri).ne, ?_⟩
  intro h hh
  refine ⟨fun hh0 => ha.injOn hh (Ioo_subset_Icc_self hri) (hh0.trans he.symm), ?_⟩
  rintro rfl
  exact he

/-- At the centered root the outer slope is strictly positive by convexity.
Strict decrease then orders the two transition floors. -/
theorem ordered_endpoint_roots {s : Set ℝ} {P : ℝ → ℝ} {c b : ℝ}
    (hc : c ∈ s) (hb : b ∈ s) (ha : StrictAntiOn P s)
    (hpc : 0 < P c) (hpb : P b = 0) : c < b := by
  by_contra! h
  have hp := ha.antitoneOn hb hc h
  linarith

/-- If each endpoint slope decreases in both arguments, its root floor
strictly decreases as the Gaussian parameter increases. -/
theorem strictAntiOn_endpoint_roots {Q H : Set ℝ} {P : ℝ → ℝ → ℝ} {r : ℝ → ℝ}
    (hm : ∀ q ∈ Q, r q ∈ H) (hz : ∀ q ∈ Q, P q (r q) = 0)
    (hq : ∀ h ∈ H, StrictAntiOn (fun q => P q h) Q)
    (hh : ∀ q ∈ Q, StrictAntiOn (P q) H) :
    StrictAntiOn r Q := by
  intro q₁ h₁ q₂ h₂ hq₁₂
  have hn := hq (r q₁) (hm q₁ h₁) h₁ h₂ hq₁₂
  by_contra! h
  have hm' := (hh q₂ h₂).antitoneOn (hm q₁ h₁) (hm q₂ h₂) h
  change P q₂ (r q₁) < P q₁ (r q₁) at hn
  rw [hz q₁ h₁] at hn
  rw [hz q₂ h₂] at hm'
  linarith

/-- The change from the Chebyshev abscissa to gap has a nonzero derivative
throughout the full interval in which either simple root occurs. -/
theorem hasDerivAt_slope_in_floor {P : ℝ → ℝ} {D h : ℝ}
    (hP : HasDerivAt P D (Real.cos (2*Real.pi*h))) :
    HasDerivAt (fun h => P (Real.cos (2*Real.pi*h)))
      (D * (-Real.sin (2*Real.pi*h) * (2*Real.pi))) h := by
  exact hP.comp h ((Real.hasDerivAt_cos _).comp h (by
    simpa using (hasDerivAt_id h).const_mul (2*Real.pi)))

theorem slope_in_floor_deriv_neg {P : ℝ → ℝ} {D h : ℝ}
    (hh : h ∈ Icc (1/8 : ℝ) (1/6)) (hD : 0 < D)
    (hP : HasDerivAt P D (Real.cos (2*Real.pi*h))) :
    deriv (fun h => P (Real.cos (2*Real.pi*h))) h < 0 := by
  have hpos : 0 < 2*Real.pi*h := by
    have : 0 < h := lt_of_lt_of_le (by norm_num) hh.1
    positivity
  have hpi : 2*Real.pi*h < Real.pi := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh.2), Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hpos hpi
  rw [(hasDerivAt_slope_in_floor hP).deriv]
  exact mul_neg_of_pos_of_neg hD (mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (by positivity))

end GaussianChains.PackedFace
