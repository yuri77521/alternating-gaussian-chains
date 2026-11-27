import StripProjection
import StripSmallFloors
import PackedFaceModesEnergy
import PackedFaceGapLink
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The amplitude lower bound for an actual global minimizer is obtained by
comparison with the centered pair of packed triples. -/
noncomputable section
namespace GaussianChains.Strip
open GaussianChains.PackedFace Real

private theorem centered_first (h : ℝ) : ‖structureFactor (sites h 0) 1‖^2 =
    4*(2*cos (2*π*h)-1)^2 := by
  rw [structureFactor_sites_sq]
  norm_num [amplitude]
  <;> ring

set_option maxHeartbeats 1000000 in
theorem first_mode_selection {s h : ℝ} (hs : 0<s) (hh : 0 ≤ h)
    {x : Fin 6 → ℝ} (hx : Feasible (by decide) h x)
    (hmin : ∀ y : Fin 6 → ℝ, Feasible (by decide) h y → imageEnergy s x ≤ imageEnergy s y) :
    let q := exp (-(π^2)/s)
    4*(2*cos (2*π*h)-1)^2 - (16*q^3+4*highTail 2 q) ≤ ‖structureFactor x 1‖^2 := by
  let q := exp (-(π^2)/s)
  have hq : 0 < q := exp_pos _
  have hq1 : q < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos pi_pos)) hs)
  have hfeas : Feasible (by decide) h (sites h 0) := by
    rw [all_gaps_iff,feasible,bound,abs_zero]
    have := floor_le_mean hx
    norm_num at this
    linarith
  have he := hmin _ hfeas
  rw [imageEnergy_fourier 3 hs x,imageEnergy_fourier 3 hs (sites h 0),sub_le_sub_iff_left] at he
  let f (y : Fin 6 → ℝ) (k : ℕ) := q^((k+1)^2)*‖structureFactor y (k+1)‖^2
  have hf (y : Fin 6 → ℝ) : Summable (f y) := fourier_summable y hs
  have hm : (∑' k, f (sites h 0) k) ≤ ∑' k, f x k :=
    (mul_le_mul_iff_right₀ (by positivity : 0 < 2*sqrt (π/s)/((2*3:ℕ):ℝ))).mp he
  have ht : q*(4*(2*cos (2*π*h)-1)^2) ≤ ∑' k, f (sites h 0) k := by
    rw [(hf _).tsum_eq_zero_add]
    have h0 : f (sites h 0) 0 = q*(4*(2*cos (2*π*h)-1)^2) := by simp [f,centered_first]
    rw [h0]
    exact le_add_of_nonneg_right (tsum_nonneg fun k => by dsimp [f]; positivity)
  have hnorm := structureFactor_le_two_mul (fun i => hh.trans (hx i))
  have hsecond : f x 1 ≤ q^4*16 := by
    have hh2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm 2) 2
    have hmul := mul_le_mul_of_nonneg_left hh2 (pow_nonneg hq.le 4)
    norm_num at hmul
    exact hmul
  have hhigh (k : ℕ) : f x (k+2) ≤ (4*q)*tailTerm 2 q k := by
    let n := k+3
    have hh' := pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2
    have hexp : q^(n^2) = q*q^(n^2-1) := by
      rw [← pow_succ',Nat.sub_add_cancel (by exact Nat.succ_le_of_lt (pow_pos (by dsimp [n]; omega) _) : 1 ≤ n^2)]
    change q^(n^2)*‖structureFactor x n‖^2 ≤ (4*q)*((n:ℝ)^2*q^(n^2-1))
    rw [hexp]
    nlinarith only [mul_le_mul_of_nonneg_left hh' (mul_nonneg hq.le (pow_nonneg hq.le (n^2-1)))]
  have htail : Summable (tailTerm 2 q) :=
    (summable_nat_add_iff 1).mpr (summable_widthMoment 2 hq.le hq1)
  have hs' := ((summable_nat_add_iff 2).mpr (hf x)).tsum_le_tsum hhigh (htail.mul_left (4*q))
  rw [tsum_mul_left] at hs'
  change _ ≤ 4*q*highTail 2 q at hs'
  have hraw := ht.trans hm
  rw [(hf x).tsum_eq_zero_add,((summable_nat_add_iff 1).mpr (hf x)).tsum_eq_zero_add] at hraw
  have hzero : f x 0 = q*‖structureFactor x 1‖^2 := by simp [f]
  rw [hzero] at hraw
  change _ ≤ q*‖structureFactor x 1‖^2 + (f x 1 + ∑' k : ℕ, f x (k+2)) at hraw
  apply (mul_le_mul_iff_right₀ hq).mp
  nlinarith only [hraw,hsecond,hs']

theorem broad_minimizer_amplitude {s h : ℝ} (h8 : 8 ≤ s) (h9 : s ≤ 9)
    (hh : 0 ≤ h) (hr : h ≤ 7/100) {x : Fin 6 → ℝ} (hx : Feasible (by decide) h x)
    (hmin : ∀ y : Fin 6 → ℝ, Feasible (by decide) h y → imageEnergy s x ≤ imageEnergy s y) :
    141/100 < ‖structureFactor x 1‖ := by
  have hselect := first_mode_selection (by linarith : 0<s) hh hx hmin
  have hb := (broad_tail_constants h8 h9).1
  have he : 2*π*h ≤ 44/100 := by
    calc _ ≤ 2*(3.1416:ℝ)*(7/100) := by gcongr; exact pi_lt_d4.le
         _ ≤ _ := by norm_num
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2*π*h) he 2
  have hc : 806/1000 ≤ 2*cos (2*π*h)-1 := by
    nlinarith only [one_sub_sq_div_two_le_cos (x:=2*π*h),hsq]
  have hc2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 806/1000) hc 2
  by_contra! H
  nlinarith only [hselect,hb,hc2,pow_le_pow_left₀ (norm_nonneg _) H 2]

theorem narrow_minimizer_amplitude {s h : ℝ} (hs : 799/100 ≤ s) (h801 : s ≤ 801/100)
    (hh : 0 ≤ h) (hr : h ≤ 1/10) {x : Fin 6 → ℝ} (hx : Feasible (by decide) h x)
    (hmin : ∀ y : Fin 6 → ℝ, Feasible (by decide) h y → imageEnergy s x ≤ imageEnergy s y) :
    1055/1000 < ‖structureFactor x 1‖ := by
  have hselect := first_mode_selection (by linarith : 0<s) hh hx hmin
  have hb := (narrow_tail_constants hs h801).1
  have he : 2*π*h ≤ π/5 := by nlinarith only [mul_le_mul_of_nonneg_left hr pi_pos.le]
  have hc := strictAntiOn_cos.antitoneOn
    (show 2*π*h ∈ Set.Icc 0 π from ⟨by positivity, by linarith [pi_pos]⟩)
    (show π/5 ∈ Set.Icc 0 π from ⟨by positivity,by linarith [pi_pos]⟩) he
  rw [cos_pi_div_five] at hc
  have hsqrt : (2236/1000:ℝ) ≤ √5 := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc' : 618/1000 ≤ 2*cos (2*π*h)-1 := by linarith
  have hc2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 618/1000) hc' 2
  by_contra! H
  nlinarith only [hselect,hb,hc2,pow_le_pow_left₀ (norm_nonneg _) H 2]

end GaussianChains.Strip
