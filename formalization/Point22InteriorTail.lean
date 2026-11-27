import CertTreeFourierCaps
import CertRootDerivative
import Point22CurvatureCertificate

/-! At width 22 the full second derivative is within 25/4 of its first two
harmonics. Six such errors still sum to less than the central curvature margin. -/
noncomputable section
namespace GaussianChains.Point22.Interior
open Real GaussianChains.FourierBounds GaussianChains.PackedFace GaussianChains.Root22

abbrev q := nome 22
def factor : ℝ := 2*scale 22*q*(2*π)^2

def trunc₂ (x : ℝ) := -factor*cos (2*π*x) - (factor*(4*q^3))*cos (2*(2*π*x))

private theorem nome_le : q ≤ (13/20:ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (x:= (97/220:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hex : (20/13:ℝ) ≤ Real.exp (π^2/22) := by
    apply (show (20/13:ℝ) ≤ Real.exp (97/220) by linarith).trans
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_d2, sq_nonneg (π-3.14)]
  unfold q nome
  rw [neg_div, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num at *
  linarith

private theorem factor_bounds : 0 ≤ factor ∧ factor ≤ 2*(38/100:ℝ)*(13/20)*(63/10)^2 := by
  have hq := (nome_positive 22).le
  have hc : scale 22 ≤ 38/100 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num,?_⟩
    linarith [Real.pi_lt_d2]
  unfold factor
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hq)
      (sq_nonneg _)
  · gcongr
    · exact nome_le
    · linarith [Real.pi_lt_d2]

private theorem three_tail (x : ℝ) :
    |∑' n : ℕ, mode q 2 (n+2) x| ≤
      (9*(13/20:ℝ)^8)/(1-tailRatio (13/20:ℝ) 2 3) := by
  have hq := (nome_positive 22).le
  have hr : tailRatio (13/20:ℝ) 2 3 < 1 := by norm_num [tailRatio]
  obtain ⟨hs,ht⟩ := weightedMode_tail hq nome_le (by norm_num) 2 3 (by decide) hr
  have hpoint (n : ℕ) : ‖mode q 2 (n+2) x‖ ≤ weightedMode q 2 (n+3) := by
    simp only [mode, Nat.add_assoc, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (weightedMode_nonneg hq _ _)]
    exact mul_le_of_le_one_right (weightedMode_nonneg hq _ _) (abs_cos_le_one _)
  have hsn : Summable fun n : ℕ => ‖mode q 2 (n+2) x‖ :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hs
  rw [← Real.norm_eq_abs]
  refine ((norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hpoint hs)).trans (ht.trans ?_)
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hr.le)
  calc
    weightedMode q 2 3 = 9*q^8 := by norm_num [weightedMode]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq nome_le 8) (by norm_num)

theorem curvature_trunc_error (x : ℝ) : |Curvature.kernel₂ x-trunc₂ x| < 25/4 := by
  have hsum := mode_summable (nome_positive 22).le (nome_lt_one (by norm_num : 0 < (22:ℝ))) 2 x
  have hseries : Curvature.kernel₂ x = factor * series q 2 x := by
    rw [show Curvature.kernel₂ x = deriv^[2] (GaussianChains.kernel 22) x from curvatureSum_eq_deriv2 x,
      kernel_deriv_series (by norm_num : 0<(22:ℝ)) 1]
    rfl
  have hm₀ : mode q 2 0 x = -cos (2*π*x) := by
    unfold mode
    norm_num [weightedMode]
  have hm₁ : mode q 2 1 x = -(4*q^3)*cos (2*(2*π*x)) := by
    unfold mode
    norm_num [weightedMode]
    left; congr 1; ring
  have hs : series q 2 x = mode q 2 0 x + mode q 2 1 x + ∑' n : ℕ, mode q 2 (n+2) x := by
    simpa [series, Finset.sum_range_succ] using (hsum.sum_add_tsum_nat_add 2).symm
  rw [hseries,hs,hm₀,hm₁]
  have he : factor *(-cos (2*π*x)+ -(4*q^3)*cos (2*(2*π*x))+
      ∑' n : ℕ, mode q 2 (n+2) x) - trunc₂ x = factor*(∑' n : ℕ, mode q 2 (n+2) x) := by
    unfold trunc₂
    ring
  rw [he, abs_mul, abs_of_nonneg factor_bounds.1]
  exact (mul_le_mul factor_bounds.2 (three_tail x) (abs_nonneg _)
    (by norm_num)).trans_lt (by norm_num [tailRatio])

end GaussianChains.Point22.Interior
