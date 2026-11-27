import BifurcationPhysical
import CertRootExp

/-! The strict normalized inward-slope bounds on the whole open branch at width eight. -/
noncomputable section
namespace GaussianChains.Bifurcation
open GaussianChains.CertExp GaussianChains.PackedFace

private theorem sharp_weight (k : ℕ) {q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ 1/3) :
    ((2*k+3:ℕ):ℝ)^3 * q^((2*k+3)^2) ≤ (1/243:ℝ)*q*(1/2:ℝ)^k := by
  let n := 2*k+3
  have H := odd_weight_tail k (q := (3/2)*q) (by positivity) (by linarith)
  have h9 : 9 ≤ n^2 := Nat.pow_le_pow_left (show 3 ≤ n by dsimp [n]; omega) 2
  calc
    _ = (2/3:ℝ)^(n^2) * ((n:ℝ)^3 * ((3/2)*q)^(n^2)) := by
      rw [mul_pow]
      have he : (2/3:ℝ)^(n^2) * (3/2:ℝ)^(n^2) = 1 := by rw [← mul_pow]; norm_num
      linear_combination -((n:ℝ)^3*q^(n^2))*he
    _ ≤ (2/3:ℝ)^9 * ((27/256:ℝ)*((3/2)*q)*(1/2:ℝ)^k) :=
      mul_le_mul (pow_le_pow_of_le_one (by norm_num) (by norm_num) h9) H
        (by positivity) (by positivity)
    _ = _ := by ring

private theorem sharp_slope {q z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ 1/3) (hF : 0 ≤ slopeFactor z) :
    |(∑' k, oddSlopeTerm q z k)-q*slopeFactor z| ≤ (2/243)*q*slopeFactor z := by
  let c := (1/243)*q*slopeFactor z
  have bound (k : ℕ) : ‖oddSlopeTerm q z (k+1)‖ ≤ c*(1/2:ℝ)^k := by
    let n := oddMode (k+1)
    have he : n=2*k+3 := by dsimp [n,oddMode]; omega
    change |(n:ℝ)*q^(n^2)*slopeFactor (n*z)| ≤ _
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)*q^(n^2))]
    have hf := slopeFactor_odd_bound (k+1) z
    rw [abs_of_nonneg hF] at hf
    calc
      _ ≤ ((n:ℝ)*q^(n^2)) * ((n:ℝ)^2*slopeFactor z) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (n:ℝ)^3*q^(n^2)*slopeFactor z := by ring
      _ ≤ ((1/243:ℝ)*q*(1/2:ℝ)^k)*slopeFactor z := by
        rw [he]; exact mul_le_mul_of_nonneg_right (sharp_weight _ hq hQ) hF
      _ = _ := by dsimp [c]; ring
  have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left c
  have hn : Summable (fun k : ℕ => ‖oddSlopeTerm q z (k+1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) bound hg
  have hs := (summable_nat_add_iff 1).1 hn.of_norm
  have H := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum bound hg)
  rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)] at H
  have hfirst : oddSlopeTerm q z 0 = q*slopeFactor z := by simp [oddSlopeTerm,oddMode]
  rw [← hs.sum_add_tsum_nat_add 1,Finset.sum_range_one,hfirst,add_sub_cancel_left]
  convert H using 1 <;> dsimp [c] <;> ring

private theorem nome_bracket : (0.290:ℝ) < Real.exp (-(Real.pi^2)/8) ∧
    Real.exp (-(Real.pi^2)/8) < 0.292 := by
  let a : ℚ := 3.1415^2/8
  let b : ℚ := 3.1416^2/8
  have hb := (negExpBox_sound (x := b) (by norm_num [b]) (by norm_num [b])).1
  have ha := (negExpBox_sound (x := a) (by norm_num [a]) (by norm_num [a])).2
  have H : (0.290:ℚ) < (negExpBox b).1 ∧ (negExpBox a).2 < 0.292 := by decide +kernel
  have hL : (a:ℝ) ≤ Real.pi^2/8 := by
    dsimp [a]; push_cast
    nlinarith [mul_pos (sub_pos.mpr Real.pi_gt_d4) (show 0 < Real.pi+3.1415 by positivity)]
  have hU : Real.pi^2/8 ≤ (b:ℝ) := by
    dsimp [b]; push_cast
    nlinarith [mul_pos (sub_pos.mpr Real.pi_lt_d4) (show 0 < 3.1416+Real.pi by positivity)]
  rw [neg_div]
  have hl : (0.290:ℝ) < ((negExpBox b).1:ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).mpr H.1 using 1 <;> norm_num
  have hu : ((negExpBox a).2:ℝ) < 0.292 := by
    convert (Rat.cast_lt (K := ℝ)).mpr H.2 using 1 <;> norm_num
  exact ⟨hl.trans_le (hb.trans (Real.exp_le_exp.mpr (neg_le_neg hU))),
    ((Real.exp_le_exp.mpr (neg_le_neg hL)).trans ha).trans_lt hu⟩

theorem normalized_inward_bounds {h : ℝ} (hh : 0<h) (h6 : h<1/6) :
    1.49 < (deriv (fun v => imageEnergy 8 (sites v 0)) h / 4) / slopeFactor (2*Real.pi*h) ∧
    (deriv (fun v => imageEnergy 8 (sites v 0)) h / 4) / slopeFactor (2*Real.pi*h) < 1.57 := by
  let q := Real.exp (-(Real.pi^2)/8)
  let c := Real.sqrt (Real.pi/8)
  let z := 2*Real.pi*h
  have hf : (fun v => imageEnergy 8 (sites v 0)) = centeredFourier q c :=
    funext (centeredFourier_imageEnergy (by norm_num))
  have hq : (0.290:ℝ)<q ∧ q<0.292 := nome_bracket
  have hc : (0.626:ℝ)<c ∧ c<0.628 := ⟨Real.lt_sqrt_of_sq_lt (by linarith [Real.pi_gt_d4]),
    (Real.sqrt_lt' (by norm_num)).2 (by linarith [Real.pi_lt_d4])⟩
  have hF : 0 < slopeFactor z := slopeFactor_pos_of_floor hh h6
  have H := abs_le.mp (sharp_slope (q := q) (by linarith [hq.1]) (by linarith [hq.2]) hF.le)
  have lo : 1.49 < (32*Real.pi*c/3/4) * ((1-2/243)*q) := by
    have hcq := mul_lt_mul_of_pos_right hq.1 (show 0<c by linarith [hc.1])
    have hpc := mul_lt_mul_of_pos_right Real.pi_gt_d4 (show 0<c*q by positivity)
    nlinarith [mul_pos (sub_pos.mpr hc.1) (by norm_num : 0 < (0.290:ℝ))]
  have hi : (32*Real.pi*c/3/4) * ((1+2/243)*q) < 1.57 := by
    have hcq := mul_lt_mul_of_pos_right hq.2 (show 0<c by linarith [hc.1])
    have hpc := mul_lt_mul_of_pos_right Real.pi_lt_d4 (show 0<c*q by positivity)
    nlinarith [mul_pos (sub_pos.mpr hc.2) (by norm_num : 0 < (0.292:ℝ))]
  have hp : 0 < 32*Real.pi*c/3/4 := by dsimp [c]; positivity
  rw [hf,(centeredFourier_hasDerivAt (show 0 ≤ q by linarith [hq.1]) (by linarith [hq.2]) h).deriv]
  change 1.49 < _ / slopeFactor z ∧ _ / slopeFactor z < 1.57
  constructor
  · rw [lt_div_iff₀ hF]
    have HS := mul_le_mul_of_nonneg_left H.1 hp.le
    nlinarith [mul_lt_mul_of_pos_right lo hF]
  · rw [div_lt_iff₀ hF]
    have HS := mul_le_mul_of_nonneg_left H.2 hp.le
    nlinarith [mul_lt_mul_of_pos_right hi hF]

end GaussianChains.Bifurcation
