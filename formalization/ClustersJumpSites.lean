import ClustersJumpCost
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Pi.Bounds

/-! Localization of the individual *labelled* particles from the first-mode
deficit and the floor on all cyclic gaps. The last-to-first gap is used for
the left-hand estimate at label zero. All displacements here are angular. -/
noncomputable section
namespace GaussianChains.JumpLocalization
open Real MeasureTheory Set Finset

private theorem half_gap_cost (θ : ℕ → ℝ) (k : ℕ) {t a δ : ℝ} (hδ : 0 ≤ δ)
    (ha : θ k ≤ a) (hb : a+δ ≤ θ (k+1))
    (ht : ∀ z ∈ Icc a (a+δ), |t-z| ≤ δ) :
    δ * (jumpSign k * sin t - δ) ≤ gapCost θ k := by
  have hL : a ≤ a + δ := by linarith
  have hlo := intervalIntegral.integral_mono_on (μ := volume) hL
    (intervalIntegrable_const (c := jumpSign k * sin t - δ))
    ((density_continuous k).intervalIntegrable _ _)
    (f := fun _ : ℝ => jumpSign k * sin t - δ) (g := density k) (by
      intro z hz
      have hsin := (abs_sin_sub_sin_le t z).trans (ht z hz)
      apply le_trans _ (le_max_left _ _)
      rcases abs_le.mp hsin with ⟨hl, hr⟩
      unfold jumpSign
      split_ifs <;> linarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo
  have hupper := intervalIntegral.integral_mono_interval (μ := volume) ha hL hb
    (Filter.Eventually.of_forall (density_nonneg k))
    ((density_continuous k).intervalIntegrable _ _)
  have hc : δ * (jumpSign k * sin t - δ) ≤ ∫ z in a..a+δ, density k z := by
    simpa only [add_sub_cancel_left] using hlo
  exact hc.trans hupper

/-- Both signs of sine are tested at each jump by its two adjacent half-gaps. -/
theorem sine_at_sites {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ} {h : ℝ}
    (hx : Feasible hN h x) (hh : 0 < h)
    (hJ : 2 - (structureFactor x 1).re ≤ 3*(m:ℝ)^2*(2*π*h)^2) (i : Fin (2*m)) :
    |sin (siteAngle hN x i.val)| ≤ (6*(m:ℝ)^2+1/2)*(2*π*h) := by
  let θ := siteAngle hN x
  let η := 2*π*h
  let J := 2 - (structureFactor x 1).re
  have hη : 0 < η := by dsimp [η]; positivity
  have hfloor (n : ℕ) : η ≤ θ (n+1) - θ n := siteAngle_gap_floor hx n
  have hcost (n : ℕ) (hn : n < 2*m) : gapCost θ n ≤ J := by
    change gapCost θ n ≤ 2 - (structureFactor x 1).re
    rw [← sum_gapCost_eq_deficit hN x]
    exact single_le_sum (f := gapCost θ) (fun j _ =>
      intervalIntegral.integral_nonneg (by linarith [hfloor j]) (fun t _ => density_nonneg j t))
      (mem_range.mpr hn)
  let p := if i.val = 0 then 2*m-1 else i.val-1
  have hi := i.isLt
  have hp : p < 2*m := by dsimp [p]; split_ifs <;> omega
  have hturn : sin (θ (p+1)) = sin (θ i.val) := by
    by_cases hi0 : i.val = 0
    · have h : p+1 = 0 + 2*m := by dsimp [p]; split_ifs <;> omega
      rw [h, hi0]
      simp only [θ, siteAngle_period, sin_add_two_pi]
    · have h : p+1 = i.val := by dsimp [p]; split_ifs <;> omega
      rw [h]
  have hsign : jumpSign p = -jumpSign i.val := by
    unfold jumpSign
    dsimp [p]
    split_ifs <;> norm_num <;> omega
  have rightCost := half_gap_cost θ i.val (t := θ i.val) (a := θ i.val) (δ := η/2)
    (by positivity) le_rfl (by linarith [hfloor i.val])
    (fun z hz => abs_le.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩)
  have leftCost := half_gap_cost θ p (t := θ (p+1)) (a := θ (p+1)-η/2) (δ := η/2)
    (by positivity) (by linarith [hfloor p]) (by linarith)
    (fun z hz => abs_le.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩)
  have bound {v : ℝ} (H : η/2 * (v-η/2) ≤ J) : v ≤ (6*(m:ℝ)^2+1/2)*η := by
    change J ≤ 3 * (m:ℝ)^2 * η^2 at hJ
    by_contra! hn
    nlinarith only [mul_pos (sub_pos.mpr hn) hη, H, hJ]
  have hr := bound (rightCost.trans (hcost _ hi))
  have hl := bound (leftCost.trans (hcost _ hp))
  rw [hturn, hsign] at hl
  change |sin (θ i.val)| ≤ (6*(m:ℝ)^2+1/2)*η
  apply abs_le.mpr
  unfold jumpSign at hr hl
  split_ifs at hr hl <;> constructor <;> linarith

/-- Choose the nearest multiple of π; even multiples represent the first
endpoint of the reference semicircle, odd multiples its antipode. -/
theorem distance_to_pi_multiple (t : ℝ) :
    ∃ k : ℤ, |t-(k:ℝ)*π| ≤ π/2 * |sin t| := by
  let k := round (t/π)
  refine ⟨k, ?_⟩
  have h := mul_le_mul_of_nonneg_right (abs_sub_round (t/π)) pi_pos.le
  have he : |t/π - (k:ℝ)| * π = |t-(k:ℝ)*π| := by
    calc
      _ = |(t/π - (k:ℝ))*π| := by rw [abs_mul, abs_of_pos pi_pos]
      _ = _ := by congr 1; field_simp
  have hsmall : |t-(k:ℝ)*π| ≤ π/2 := by change |t/π - (k:ℝ)| * π ≤ _ at h; linarith [he]
  have hj := mul_abs_le_abs_sin hsmall
  rw [sin_sub_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul] at hj
  have hm := mul_le_mul_of_nonneg_left hj pi_pos.le
  field_simp [pi_ne_zero] at hm
  rw [mul_comm π (k:ℝ)] at hm
  linarith

/-- The published radius Cη for every physical site in an aligned cell. -/
theorem localized_sites {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ} {h : ℝ}
    (hx : Feasible hN h x) (hh : 0 < h)
    (hJ : 2 - (structureFactor x 1).re ≤ 3*(m:ℝ)^2*(2*π*h)^2) (i : Fin (2*m)) :
    ∃ k : ℤ, |2*π*x i - (k:ℝ)*π| ≤ (1+3*π*(m:ℝ)^2)*(2*π*h) := by
  obtain ⟨k, hk⟩ := distance_to_pi_multiple (siteAngle hN x i.val)
  refine ⟨k, ?_⟩
  have hb := hk.trans (mul_le_mul_of_nonneg_left (sine_at_sites hx hh hJ i) (by positivity))
  simp only [siteAngle, liftSite_fin] at hb
  nlinarith only [hb, mul_nonneg (sub_nonneg.mpr pi_lt_four.le) (show 0 ≤ 2*π*h by positivity)]

end GaussianChains.JumpLocalization
