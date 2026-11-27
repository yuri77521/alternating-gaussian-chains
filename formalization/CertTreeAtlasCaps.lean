import CertTreeKernelDeriv
import CertTreeFourierCaps

/-! The sharp curvature cap for the width-22 atlas. The central image contributes
exactly -44 at the origin. Every other image there contributes positive curvature. -/
noncomputable section

namespace GaussianChains.FourierBounds

open ImageCalculus Polynomial

theorem point_curvature_cap (x : ℝ) : |deriv^[2] (kernel 22) x| ≤ 44 := by
  apply (curvature_max_at_zero (by norm_num : 0 < (22:ℝ)) x).trans
  have hcmp : ∀ k : ℤ, (if k = 0 then (-44:ℝ) else 0) ≤
      imageTerm 22 ((next 22)^[2] 1) k 0 := by
    intro k
    have hval : imageTerm 22 ((next 22)^[2] 1) k 0 =
        ((44*(k:ℝ))^2 - 44) * Real.exp (-(22:ℝ)*(k:ℝ)^2) := by
      simp [imageTerm, Function.iterate_succ_apply', next, Polynomial.derivative_mul]
      ring
    rw [hval]
    split_ifs with hk
    · simp [hk]
    · apply mul_nonneg _ (Real.exp_nonneg _)
      have hk2 : (1:ℝ) ≤ (k:ℝ)^2 := by
        have hi : (1:ℤ) ≤ k^2 := by
          have hn := sq_pos_of_ne_zero hk
          omega
        exact_mod_cast hi
      nlinarith only [hk2]
  have hsum := (hasSum_ite_eq (0:ℤ) (-44:ℝ)).summable.tsum_le_tsum hcmp
    (imageTerm_summable (by norm_num : 0 < (22:ℝ)) ((next 22)^[2] 1) 0)
  rw [(hasSum_ite_eq (0:ℤ) (-44:ℝ)).tsum_eq] at hsum
  rw [kernel_iterated_deriv (by norm_num : 0 < (22:ℝ)) 2]
  change -(∑' k : ℤ, imageTerm 22 ((next 22)^[2] 1) k 0) ≤ 44
  linarith only [hsum]

/-- All three caps used to widen the piecewise-linear mesh tables at width 22. -/
theorem point_atlas_caps (x : ℝ) :
    |deriv^[2] (kernel 22) x| ≤ 44 ∧ |deriv^[3] (kernel 22) x| ≤ 1500 ∧
    |deriv^[4] (kernel 22) x| ≤ 22000 :=
  ⟨point_curvature_cap x, (point_high_derivative_caps x).1.le, (point_high_derivative_caps x).2.le⟩

end GaussianChains.FourierBounds
