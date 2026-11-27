import ClustersLocalizationDefs
import ChainFourier
import ClusterSeriesDipole

/-! The physical normalization of the semicircle deficit. -/
noncomputable section
namespace GaussianChains.Localization
open Real ClusterSeries

theorem dipole_modes_hasSum {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => q^((k+1)^2) * ‖dipoleMode (k+1)‖^2)
      (4 * parityMoment Odd q 0) := by
  apply ((parityMoment_hasSum Odd hq hq1 0).mul_left (4:ℝ)).congr_fun
  intro k
  rcases Nat.even_or_odd (k+1) with he | ho
  · simp [parityTerm, dipoleMode, he, Nat.not_odd_iff_even.mpr he]
  · simp [parityTerm, dipoleMode, ho, Nat.not_even_iff_odd.mpr ho]
    ring

/-- The Fourier expression compared in the per-mode proof is exactly
N(E−I_N)/(2cq), at every positive width, for arbitrary labelled sites. -/
theorem normalized_energy_deficit (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (x : Fin (2*m) → ℝ) :
    let N := ((2*m : ℕ):ℝ)
    let q := exp (-(π^2)/s)
    let c := sqrt (π/s)
    N*(imageEnergy s x - dipoleEnergy (2*m) s)/(2*c*q) =
      4 - ‖structureFactor x 1‖^2 - ∑' k : ℕ, q^((k+2)^2-1) *
        (‖structureFactor x (k+2)‖^2 - ‖dipoleMode (k+2)‖^2) := by
  dsimp only
  let q := exp (-(π^2)/s)
  let c := sqrt (π/s)
  let N := ((2*m : ℕ):ℝ)
  have hq : 0 < q := exp_pos _
  have hq1 : q < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hs)
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have hc : c ≠ 0 := (sqrt_pos.mpr (div_pos pi_pos hs)).ne'
  let p (k : ℕ) := ‖structureFactor x (k+1)‖^2
  let d (k : ℕ) := ‖dipoleMode (k+1)‖^2
  let wp (k : ℕ) := q^((k+1)^2)*p k
  let wd (k : ℕ) := q^((k+1)^2)*d k
  have hwp : Summable wp := fourier_summable x hs
  have hwd : HasSum wd (4*parityMoment Odd q 0) := dipole_modes_hasSum hq hq1
  have hr : (∑' k, wp k) - (∑' k, wd k) =
      q*(p 0-4) + q*(∑' k, q^((k+2)^2-1)*(p (k+1)-d (k+1))) := by
    rw [← hwp.tsum_sub hwd.summable, (hwp.sub hwd.summable).tsum_eq_zero_add]
    change wp 0 - wd 0 + (∑' k, (wp (k+1)-wd (k+1))) = _
    have h0 : wp 0 - wd 0 = q * (p 0-4) := by
      norm_num [wp,wd,d,dipoleMode,norm_mul] <;> ring
    rw [h0, ← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro k
    have hpow : q^((k+2)^2) = q*q^((k+2)^2-1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity : 0 < (k+2)^2))]
    change q^((k+2)^2)*p (k+1)- q^((k+2)^2)*d (k+1) = _
    rw [hpow]
    ring
  rw [imageEnergy_fourier m hs x, dipoleEnergy, kernel_dipole_difference hs]
  change N * ((1-2*c/N*(∑' k, wp k))-(1-2*(4*c*parityMoment Odd q 0)/N))/(2*c*q) = _
  calc
    _ = -((∑' k, wp k)-(∑' k, wd k))/q := by
      rw [hwd.tsum_eq]
      field_simp [hN,hc,hq.ne']
      <;> ring
    _ = _ := by
      rw [hr]
      change -(q*(p 0-4)+q*(∑' k, q^((k+2)^2-1)*(p (k+1)-d (k+1))))/q =
        4-p 0-(∑' k, q^((k+2)^2-1)*(p (k+1)-d (k+1)))
      field_simp [hq.ne']
      <;> ring

#print axioms normalized_energy_deficit
end GaussianChains.Localization

