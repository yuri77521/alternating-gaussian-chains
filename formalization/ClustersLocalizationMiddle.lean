import ClustersLocalizationDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

noncomputable section
namespace GaussianChains.Localization
open Real MeasureTheory Set Finset

/-- A quarter of one chart adjacent to the midpoint of either half-circle
contributes exactly sqrt(2)/2 when it is wholly in the discrepancy. -/
theorem chart_cost_lower {d : ℝ → ℝ} (hi : IntervalIntegrable d volume 0 (π/2))
    (hd : ∀ t ∈ Icc 0 (π/2), 0 ≤ d t)
    (hbad : ∀ t ∈ Icc (π/4) (π/2), d t = 1) :
    sqrt 2/2 ≤ ∫ t in 0..π/2, sin t * d t := by
  have h0 : 0 ≤ π/4 := by positivity
  have hT : π/4 ≤ π/2 := by linarith [pi_pos]
  have hk := intervalIntegral.integral_mono_interval (f := fun t => sin t * d t)
    h0 hT le_rfl (μ := volume)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall (by
      intro t ht
      exact mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2,pi_pos]))
        (hd t (Ioc_subset_Icc_self ht)))))
    (hi.continuousOn_mul continuous_sin.continuousOn)
  have heq : (∫ t in π/4..π/2, sin t*d t) = ∫ t in π/4..π/2, sin t :=
    intervalIntegral.integral_congr (by
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp [hbad t ht])
  rw [heq, integral_sin, cos_pi_div_four, cos_pi_div_two, sub_zero] at hk
  exact hk

/-- For any two distinct radial charts at least one has a point consistent
with the reference occupation in its middle part whenever J < sqrt(2).
Taking (0,1) and (2,3) supplies one middle cut in each semicircle. -/
theorem exists_central_agreement (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t) {i j : Fin 4} (hne : i ≠ j)
    (hsmall : arcCost d < sqrt 2) :
    ∃ k : Fin 4, (k = i ∨ k = j) ∧ ∃ t ∈ Icc (π/4) (π/2), d k t ≠ 1 := by
  by_contra! h
  let c (k : Fin 4) := ∫ t in 0..π/2, sin t * d k t
  have hi' : sqrt 2/2 ≤ c i := chart_cost_lower (hi i) (hd i) (h i (Or.inl rfl))
  have hj' : sqrt 2/2 ≤ c j := chart_cost_lower (hi j) (hd j) (h j (Or.inr rfl))
  have hNN (k : Fin 4) : 0 ≤ c k := intervalIntegral.integral_nonneg (by positivity)
    fun t ht => mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,pi_pos])) (hd k t ht)
  have hsum : ∑ k ∈ ({i,j} : Finset (Fin 4)), c k ≤ ∑ k, c k :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ => hNN k
  simp [hne] at hsum
  change ∑ k, c k < sqrt 2 at hsmall
  linarith only [hi', hj', hsum, hsmall]

/-- Check the strict middle-arc cost threshold at the published floor.
The weaker consequence 2mη ≤ 1 already suffices for this step. -/
theorem smallFloor_cost_lt_sqrt_two {J m η : ℝ} (hm : 1 ≤ m) (hη : 0 ≤ η)
    (hfloor : η ≤ 1/(2*m*(1+3*π*m^2)^2)) (hJ : J ≤ 3*m^2*η^2) :
    J < sqrt 2 := by
  have hpos : 0 < 2*m := by linarith
  have hC : 1 ≤ 1+3*π*m^2 := by linarith only [mul_nonneg (by positivity : 0 ≤ 3*π) (sq_nonneg m)]
  have hC2 : 1 ≤ (1+3*π*m^2)^2 := one_le_pow₀ hC
  have hsmall := (le_div_iff₀ (mul_pos hpos (lt_of_lt_of_le zero_lt_one hC2))).1 hfloor
  have hη' : η*(2*m) ≤ 1 := by
    nlinarith only [hsmall, mul_nonneg (mul_nonneg hη hpos.le) (sub_nonneg.mpr hC2)]
  have hs := pow_le_pow_left₀ (mul_nonneg hη hpos.le) hη' 2
  have hroot : 1 ≤ sqrt 2 := by norm_num
  nlinarith only [hs,hJ,hroot]

end GaussianChains.Localization

