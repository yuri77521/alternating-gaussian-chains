import ArcQuadrants
import ClustersLocalizationDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! For the reference semicircle (0,π), crossing its boundary reverses the
sign of the indicator discrepancy. The chart mode equals the actual Fourier
integral for every positive integer frequency. -/

noncomputable section
namespace GaussianChains.Localization
open Real MeasureTheory Set

def chartDiscrepancy (a : ℝ → ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  if i.val < 2 then 1 - a (quadrantAngle i t) else a (quadrantAngle i t)

private theorem osc_add' (n : ℕ) (t u : ℝ) :
    osc n (t + u) = osc n t * osc n u := by
  unfold osc
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem osc_pi' (n : ℕ) : osc n π = (-1 : ℂ)^n := by
  simp [osc, mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private theorem osc_two_pi' (n : ℕ) : osc n (2*π) = 1 := by
  rw [two_mul, osc_add', osc_pi', ← mul_pow]
  simp

private theorem chartWave_eq_signed (n : ℕ) (i : Fin 4) (t : ℝ) :
    chartWave n i t = if i.val < 2 then -osc n (quadrantAngle i t)
      else osc n (quadrantAngle i t) := by
  fin_cases i <;> simp [chartWave, quadrantAngle, sub_eq_add_neg, osc_add', osc_pi', osc_two_pi']

private theorem osc_cont (n : ℕ) : Continuous (osc n) := by
  unfold osc
  fun_prop

private theorem weighted_osc_int (n : ℕ) (a : ℝ → ℝ) {u v : ℝ}
    (ha : IntervalIntegrable a volume u v) :
    IntervalIntegrable (fun t => a t • osc n t) volume u v := by
  have hc : IntervalIntegrable (fun t => (a t : ℂ)) volume u v :=
    ⟨ha.1.ofReal, ha.2.ofReal⟩
  simpa [Complex.real_smul] using hc.mul_continuousOn (osc_cont n).continuousOn

theorem semicircle_integral_mode {n : ℕ} (hn : 0 < n) :
    (n : ℝ) • (∫ t in 0..π, osc n t) = dipoleMode n := by
  have hN : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have rep (t : ℝ) : osc n t = Complex.exp (((n:ℂ) * Complex.I) * t) := by
    unfold osc
    congr 1
    push_cast
    ring
  simp_rw [rep]
  rw [integral_exp_mul_complex (mul_ne_zero hN Complex.I_ne_zero), ← rep π]
  simp only [Complex.real_smul, Complex.ofReal_natCast, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, osc_pi']
  rw [show (n:ℂ)*(((-1:ℂ)^n - 1)/((n:ℂ)*Complex.I)) =
      ((-1:ℂ)^n - 1)/Complex.I by field_simp, Complex.div_I]
  by_cases he : Even n
  · simp [dipoleMode, he, he.neg_one_pow]
  · simp [dipoleMode, he, (Nat.not_even_iff_odd.mp he).neg_one_pow]
    ring

theorem chartDiscrepancy_integrable (a : ℝ → ℝ) (ha : ∀ u v, IntervalIntegrable a volume u v)
    (i : Fin 4) : IntervalIntegrable (chartDiscrepancy a i) volume 0 (π/2) := by
  change IntervalIntegrable (fun t => if i.val < 2 then 1 - a (quadrantAngle i t)
    else a (quadrantAngle i t)) volume 0 (π/2)
  by_cases h : i.val < 2
  · simpa [chartDiscrepancy, h] using
      (intervalIntegrable_const (c := (1:ℝ))).sub (quadrant_intervalIntegrable a ha i)
  · simpa [chartDiscrepancy, h] using quadrant_intervalIntegrable a ha i

theorem chartDiscrepancy_range (a : ℝ → ℝ) (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1)
    (i : Fin 4) (t : ℝ) : 0 ≤ chartDiscrepancy a i t ∧ chartDiscrepancy a i t ≤ 1 := by
  obtain ⟨hl, hr⟩ := ha (quadrantAngle i t)
  by_cases h : i.val < 2 <;> simp [chartDiscrepancy, h] <;> constructor <;> linarith

/-- Four changes of variables express the whole occupancy mode as the
semicircle mode plus the signed mass on the four discrepancy charts. -/
theorem occupancy_integral_eq_arcMode {n : ℕ} (hn : 0 < n) (a : ℝ → ℝ)
    (ha : ∀ u v, IntervalIntegrable a volume u v) :
    (n : ℝ) • (∫ t in 0..2*π, a t • osc n t) = arcMode n (chartDiscrepancy a) := by
  let F (t : ℝ) := a t • osc n t
  have hF (u v : ℝ) : IntervalIntegrable F volume u v := weighted_osc_int n a (ha u v)
  have hW (u v : ℝ) : IntervalIntegrable (osc n) volume u v :=
    (osc_cont n).intervalIntegrable _ _
  have chart (i : Fin 4) :
      (∫ t in 0..π/2, F (quadrantAngle i t)) =
        (if i.val < 2 then (∫ t in 0..π/2, osc n (quadrantAngle i t)) else 0) +
        ∫ t in 0..π/2, chartDiscrepancy a i t • chartWave n i t := by
    by_cases h : i.val < 2
    · simp_rw [chartDiscrepancy, chartWave_eq_signed, if_pos h, smul_neg, sub_smul, one_smul,
        neg_sub]
      rw [intervalIntegral.integral_sub (quadrant_intervalIntegrable F hF i)
        (quadrant_intervalIntegrable (osc n) hW i)]
      abel
    · simp [chartDiscrepancy, chartWave_eq_signed, h, F]
  have half : (∑ i : Fin 4, if i.val < 2 then
      (∫ t in 0..π/2, osc n (quadrantAngle i t)) else 0) = ∫ t in 0..π, osc n t := by
    simpa [Fin.sum_univ_four] using (integral_upper_quadrants (osc n) hW).symm
  change (n : ℝ) • (∫ t in 0..2*π, F t) = _
  rw [integral_quadrants F hF]
  simp_rw [chart]
  rw [Finset.sum_add_distrib, half, smul_add, semicircle_integral_mode hn]
  rfl

end GaussianChains.Localization
