import ClustersArcCharts
import Mathlib.Data.Set.SymmDiff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The sharp sine-weighted symmetric-difference estimate stated immediately
after Eq. (3). On each radial chart compare occupation with the indicator of
[0,a], using the same a on all four charts. -/
noncomputable section
namespace GaussianChains.Localization
open Real MeasureTheory Set Finset
open scoped symmDiff

private theorem sine_support {a : ℝ} (ha : a ∈ Icc 0 (π/2)) {d : ℝ → ℝ}
    (hi : IntervalIntegrable d volume 0 (π/2))
    (hd : ∀ t ∈ Icc 0 (π/2), 0 ≤ d t ∧ d t ≤ 1) :
    (1-cos a) + sin a*((∫ t in 0..π/2, d t)-a) ≤
      ∫ t in 0..π/2, sin t*d t := by
  have hT : 0 ≤ π/2 := by positivity
  have il : IntervalIntegrable d volume 0 a :=
    hi.mono_set (by simpa [uIcc_of_le hT, uIcc_of_le ha.1] using Icc_subset_Icc le_rfl ha.2)
  have ir : IntervalIntegrable d volume a (π/2) :=
    hi.mono_set (by simpa [uIcc_of_le hT, uIcc_of_le ha.2] using Icc_subset_Icc ha.1 le_rfl)
  have pl := il.continuousOn_mul continuous_sin.continuousOn
  have pr := ir.continuousOn_mul continuous_sin.continuousOn
  have hl := intervalIntegral.integral_mono_on ha.1
    ((continuous_sin.sub continuous_const).intervalIntegrable _ _) (pl.sub (il.const_mul (sin a)))
    (f := fun t => sin t-sin a) (g := fun t => sin t*d t - sin a*d t) (by
      intro t ht
      have hm := sin_le_sin_of_le_of_le_pi_div_two (by linarith [ht.1, pi_pos]) ha.2 ht.2
      have h1 := (hd t ⟨ht.1, ht.2.trans ha.2⟩).2
      nlinarith only [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr h1)])
  have hr := intervalIntegral.integral_mono_on ha.2 (ir.const_mul (sin a)) pr
    (f := fun t => sin a*d t) (g := fun t => sin t*d t) (by
      intro t ht
      exact mul_le_mul_of_nonneg_right
        (sin_le_sin_of_le_of_le_pi_div_two (by linarith [ha.1,pi_pos]) ht.2 ht.1)
        (hd t ⟨ha.1.trans ht.1,ht.2⟩).1)
  dsimp only at hl hr
  rw [intervalIntegral.integral_sub (f := sin) (g := fun _ => sin a)
        (continuous_sin.intervalIntegrable _ _) intervalIntegrable_const,
      integral_sin, cos_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      intervalIntegral.integral_sub pl (il.const_mul _), intervalIntegral.integral_const_mul] at hl
  rw [intervalIntegral.integral_const_mul] at hr
  rw [← intervalIntegral.integral_add_adjacent_intervals pl pr,
      ← intervalIntegral.integral_add_adjacent_intervals il ir]
  linarith only [hl, hr]

/-- The symmetric difference of angular measure b has cost at least
4(1−cos(b/4)). This holds even for fractional occupation densities. -/
theorem sharp_discrepancy_cost (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t ∧ d i t ≤ 1) :
    4 * (1 - cos (arcMass d/4)) ≤ arcCost d := by
  let a := arcMass d/4
  have hT : 0 ≤ π/2 := by positivity
  have hl (i : Fin 4) : 0 ≤ ∫ t in 0..π/2, d i t :=
    intervalIntegral.integral_nonneg hT (fun t ht => (hd i t ht).1)
  have hu (i : Fin 4) : (∫ t in 0..π/2, d i t) ≤ π/2 := by
    simpa using intervalIntegral.integral_mono_on hT (hi i)
      (intervalIntegrable_const (c := (1:ℝ))) (fun t ht => (hd i t ht).2)
  have ha : a ∈ Icc 0 (π/2) := by
    constructor
    · exact div_nonneg (sum_nonneg (fun i _ => hl i)) (by norm_num)
    · have hsum := sum_le_sum (s := (univ : Finset (Fin 4))) fun i _ => hu i
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hsum
      dsimp only [a, arcMass]
      linarith
  have h := sum_le_sum (s := (univ : Finset (Fin 4))) fun i _ => sine_support ha (hi i) (hd i)
  rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_sub_distrib] at h
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h
  change 4*1 - 4*cos a + sin a*(arcMass d - 4*a) ≤ arcCost d at h
  rw [show arcMass d-4*a=0 by dsimp [a]; ring, mul_zero, add_zero] at h
  change 4*(1-cos a) ≤ arcCost d
  linarith only [h]

/-- In the four radial charts the discrepancy is precisely the indicator
of the symmetric difference, away from the two endpoints of the semicircle. -/
theorem chartDiscrepancy_symmDiff (A : Set ℝ) (i : Fin 4) {t : ℝ}
    (ht : t ∈ Ioc 0 (π/2)) :
    chartDiscrepancy (occupied A) i t = occupied (A ∆ Ioo 0 π) (quadrantAngle i t) := by
  have hchart : quadrantAngle i t ∈ Ioo 0 π ↔ i.val < 2 := by
    fin_cases i
    · change (0 < t ∧ t < π) ↔ (0:ℕ) < 2
      exact iff_of_true ⟨ht.1, by linarith [ht.2,pi_pos]⟩ (by decide)
    · change (0 < π-t ∧ π-t < π) ↔ (1:ℕ) < 2
      exact iff_of_true ⟨by linarith [ht.2,pi_pos], by linarith [ht.1]⟩ (by decide)
    · change (0 < π+t ∧ π+t < π) ↔ (2:ℕ) < 2
      exact iff_of_false (fun h => by linarith [h.2,ht.1]) (by decide)
    · change (0 < 2*π-t ∧ 2*π-t < π) ↔ (3:ℕ) < 2
      exact iff_of_false (fun h => by linarith [h.2,ht.2,pi_pos]) (by decide)
  by_cases hp : i.val < 2 <;> by_cases hA : quadrantAngle i t ∈ A <;>
    simp [chartDiscrepancy, occupied, Set.mem_symmDiff, hchart, hp, hA]

private theorem chart_sine_abs (i : Fin 4) {t : ℝ} (ht : t ∈ Ioc 0 (π/2)) :
    |sin (quadrantAngle i t)| = sin t := by
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2,pi_pos])
  fin_cases i <;> simp [quadrantAngle, abs_of_nonneg hs, Real.sin_sub, Real.sin_add]

/-- Sharp discrepancy formula for an arbitrary measurable set on one full
period. An integral of the indicator gives angular measure of A△H. -/
theorem semicircle_symmDiff_cost {A : Set ℝ} (hA : MeasurableSet A) :
    let B := A ∆ Ioo 0 π
    4*(1 - cos ((∫ t in 0..2*π, occupied B t)/4)) ≤
      ∫ t in 0..2*π, |sin t| * occupied B t := by
  dsimp only
  let B := A ∆ Ioo 0 π
  let d := chartDiscrepancy (occupied A)
  have hB : MeasurableSet B := hA.symmDiff measurableSet_Ioo
  have hT : 0 ≤ π/2 := by positivity
  have hmass : (∫ t in 0..2*π, occupied B t) = arcMass d := by
    rw [integral_quadrants _ (occupied_intervalIntegrable hB)]
    apply sum_congr rfl
    intro i _
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hT] at ht
    exact (chartDiscrepancy_symmDiff A i ht).symm
  have hcost : (∫ t in 0..2*π, |sin t| * occupied B t) = arcCost d := by
    have hi (a b : ℝ) := (occupied_intervalIntegrable hB a b).continuousOn_mul
      (continuous_sin.abs.continuousOn)
    rw [integral_quadrants _ hi]
    apply sum_congr rfl
    intro i _
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hT] at ht
    change |sin (quadrantAngle i t)| * occupied (A ∆ Ioo 0 π) (quadrantAngle i t) =
      sin t * chartDiscrepancy (occupied A) i t
    rw [chart_sine_abs i ht, ← chartDiscrepancy_symmDiff A i ht]
  change 4*(1-cos ((∫ t in 0..2*π, occupied B t)/4)) ≤ _
  rw [hmass,hcost]
  exact sharp_discrepancy_cost d (chartDiscrepancy_integrable _ (occupied_intervalIntegrable hA))
    (fun i t _ => chartDiscrepancy_range _ (occupied_mem_Icc A) i t)

#print axioms sharp_discrepancy_cost
#print axioms semicircle_symmDiff_cost
end GaussianChains.Localization

