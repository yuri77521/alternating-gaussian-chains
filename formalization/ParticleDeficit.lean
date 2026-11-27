import ArcOccupation
import ClustersArcCharts
import ClustersLocalizationModes
import ClustersRotation
import ClustersWidth

/-! A mode-by-mode semicircle comparison for the physical alternating cell. -/
noncomputable section
namespace GaussianChains.Occupation
open Real MeasureTheory Set Localization

def charts {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) : Fin 4 → ℝ → ℝ :=
  chartDiscrepancy (occupied (circleSet hN x))

theorem arcMode_eq_I_structureFactor {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) (n : ℕ) (hn : 0 < n) :
    arcMode n (charts hN x) = Complex.I * structureFactor x n := by
  rw [charts, ← occupancy_integral_eq_arcMode hn _
    (occupied_intervalIntegrable (measurable_circleSet hN x)), structureFactor_eq_periodicIntegral hx n hn]
  have rep (t : ℝ) : occupied (circleSet hN x) t • osc n t =
      (circleSet hN x).indicator (fun u : ℝ => Complex.exp (((n:ℂ)*Complex.I)*(u:ℂ))) t := by
    classical
    by_cases h : t ∈ circleSet hN x
    · simp only [occupied, h, indicator_of_mem, one_smul]
      unfold osc
      congr 1
      push_cast
      ring
    · simp [occupied, h]
  simp_rw [rep]
  rw [Complex.real_smul]
  push_cast
  have algebra (z : ℂ) : (n:ℂ)*z = Complex.I * (-((n:ℂ)*Complex.I)*z) := by
    rw [show Complex.I * (-((n:ℂ)*Complex.I)*z) = -(Complex.I*Complex.I) * ((n:ℂ)*z) by ring,
      Complex.I_mul_I]
    ring
  exact algebra _

/-- The cost measured on the real particle arcs is exactly the projected
first-mode deficit. With an aligned cell this projection is its norm. -/
theorem chart_cost_eq {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ} (hx : Feasible hN 0 x) :
    arcCost (charts hN x) = 2 - (structureFactor x 1).re := by
  have hi := chartDiscrepancy_integrable (occupied (circleSet hN x))
    (occupied_intervalIntegrable (measurable_circleSet hN x))
  have h := arcMode_one_im (charts hN x) hi
  rw [arcMode_eq_I_structureFactor hx 1 (by decide), Complex.mul_im] at h
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h
  linarith

theorem chart_cost_nonneg {m : ℕ} (hN : 0 < 2*m) (x : Fin (2*m) → ℝ) :
    0 ≤ arcCost (charts hN x) := by
  apply Finset.sum_nonneg
  intro i _
  apply intervalIntegral.integral_nonneg (by positivity)
  intro t ht
  exact mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,pi_pos]))
    (chartDiscrepancy_range _ (occupied_mem_Icc (circleSet hN x)) i t).1

theorem structureFactor_one_le_two {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) : ‖structureFactor x 1‖ ≤ 2 := by
  obtain ⟨a,hy,_,halign,_⟩ := exists_first_mode_aligned hN x 0 1 hx
  have h := chart_cost_nonneg hN (fun i => x i-a)
  rw [chart_cost_eq hy, halign, Complex.ofReal_re] at h
  linarith
/-- The semicircle deficit for the structure factors of every feasible
collision-closure cell. The zeroth summation index is frequency two. -/
theorem physical_semicircle_deficit {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ}
    (hx : Feasible hN 0 x) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hR : widthR q ≤ 2/3) :
    (4 - ‖structureFactor x 1‖^2)/3 ≤
      4 - ‖structureFactor x 1‖^2 -
        ∑' k : ℕ, q^((k+2)^2-1) * (‖structureFactor x (k+2)‖^2 - ‖dipoleMode (k+2)‖^2) := by
  obtain ⟨a,hy,_,halign,hnorm⟩ := exists_first_mode_aligned hN x 0 1 hx
  let y := fun i => x i - a
  let A := circleSet hN y
  let d := charts hN y
  have hi := chartDiscrepancy_integrable (occupied A) (occupied_intervalIntegrable
    (measurable_circleSet hN y))
  have hd := chartDiscrepancy_range (occupied A) (occupied_mem_Icc A)
  have hmode (n : ℕ) (hn : 0 < n) : arcMode n d = Complex.I * structureFactor y n :=
    arcMode_eq_I_structureFactor hy n hn
  have hfirst : arcMode 1 d = Complex.I * (‖structureFactor x 1‖:ℂ) := by rw [hmode _ (by decide)]; exact congrArg _ halign
  let w := fun k : ℕ => q^((k+2)^2-1)
  have hw : Summable (fun k : ℕ => w k * ((k+2:ℕ):ℝ)^4) := by
    simpa [w, mul_comm] using summable_widthMoment 4 hq0 hq1
  have hR' : (∑' k : ℕ, w k * ((k+2:ℕ):ℝ)^4) ≤ 2/3 := by
    simpa [widthR, widthTerm, w, mul_comm] using hR
  have H := arc_semicircle_deficit d hi (fun i t _ => hd i t)
    (by rw [hfirst]; simp) (by rw [hfirst]; simp) w (fun k => pow_nonneg hq0 _) hw hR'
  have hnmode (n : ℕ) (hn : 0 < n) : ‖arcMode n d‖ = ‖structureFactor x n‖ := by
    rw [hmode n hn, norm_mul, Complex.norm_I, one_mul]
    exact hnorm n
  have htail (k : ℕ) : modeLoss (k+2) d =
      ‖structureFactor x (k+2)‖^2 - ‖dipoleMode (k+2)‖^2 := by
    rw [modeLoss, hnmode (k+2) (by omega)]
  simpa only [w, hnmode 1 (by decide), htail] using H

#print axioms physical_semicircle_deficit
end GaussianChains.Occupation
