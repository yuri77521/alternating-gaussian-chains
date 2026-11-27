import ClusterSeriesCosine
import CertTreeVariations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! A first-harmonic peak test using both stationarity and the curvature sign:
a point near the opposite zero of the sine is ruled out by the second test. -/
namespace GaussianChains.Strip
open Real

theorem two_derivative_peak {f : ℝ → ℝ} {z u A d e₁ e₂ : ℝ}
    (hm : IsLocalMax f z) (hc : ContinuousAt f z) (hA : 0 < A)
    (hd : 0 ≤ d) (hd' : d ≤ π/2) (hu : |u| ≤ π)
    (hfirst : |deriv f z+A*sin u| ≤ e₁) (hsecond : |deriv (deriv f) z+A*cos u| ≤ e₂)
    (hs : e₁ < A*sin d) (hcos : e₂ < A*cos d) : |u| < d := by
  obtain ⟨hslope,hcurv⟩ := Cert.necessary_transfer hm hc
  rw [hslope,zero_add,abs_mul,abs_of_pos hA] at hfirst
  have hsinu := (mul_lt_mul_iff_right₀ hA).mp (hfirst.trans_lt hs)
  have hcB := (abs_le.mp hsecond).1
  have hcosu : -cos d < cos u := by
    apply (mul_lt_mul_iff_right₀ hA).mp
    linarith
  have hsq := pow_lt_pow_left₀ hsinu (abs_nonneg _) (by decide : 2 ≠ 0)
  rw [sq_abs] at hsq
  have hdcos : 0 ≤ cos d := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos],hd'⟩
  have hleft : 0 < cos u+cos d := by linarith
  have hdiff : cos d < cos u := by
    by_contra! hh
    nlinarith only [hsq,sin_sq_add_cos_sq d,sin_sq_add_cos_sq u,
      mul_nonneg hleft.le (sub_nonneg.mpr hh)]
  by_contra! hu'
  have hm := strictAntiOn_cos.antitoneOn
    (show d ∈ Set.Icc 0 π from ⟨hd,by linarith [pi_pos]⟩)
    (show |u| ∈ Set.Icc 0 π from ⟨abs_nonneg _,hu⟩) hu'
  rw [cos_abs] at hm
  linarith

theorem broad_peak_tests {A : ℝ} (hA : 141/100 < A) :
    (616/1000 : ℝ) < A*sin (46/100) ∧ (1246/1000 : ℝ) < A*cos (46/100) := by
  have hs := (abs_le.mp (ClusterSeries.sin_linear_bound (46/100))).1
  norm_num [abs_of_nonneg] at hs
  have hc := one_sub_sq_div_two_le_cos (x:=46/100)
  have hs' : 0 < sin (46/100) := by linarith
  have hc' : 0 < cos (46/100) := by linarith
  exact ⟨by nlinarith only [hs,mul_lt_mul_of_pos_right hA hs'],
         by nlinarith only [hc,mul_lt_mul_of_pos_right hA hc']⟩

theorem narrow_peak_tests {A : ℝ} (hA : 1055/1000 < A) :
    (41/100 : ℝ) < A*sin (42/100) ∧ (82/100 : ℝ) < A*cos (42/100) := by
  have hs := (abs_le.mp (ClusterSeries.sin_linear_bound (42/100))).1
  norm_num [abs_of_nonneg] at hs
  have hc := one_sub_sq_div_two_le_cos (x:=42/100)
  have hs' : 0 < sin (42/100) := by linarith
  have hc' : 0 < cos (42/100) := by linarith
  exact ⟨by nlinarith only [hs,mul_lt_mul_of_pos_right hA hs'],
         by nlinarith only [hc,mul_lt_mul_of_pos_right hA hc']⟩

end GaussianChains.Strip
