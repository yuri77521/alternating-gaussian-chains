import StripFiveOnePowers
import ClustersTwo
import StripSmallFloors
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Comparisons with a packed five-site block, including all higher modes.
The displacement v and the gap η in this module are angular. -/
noncomputable section
namespace GaussianChains.Strip
open Real

def normalizedMass (q : ℝ) (F : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, q^((k+1)^2-1)*F (k+1)

private def powerBound (F : ℕ → ℝ) := ∀ n, 0 ≤ F n ∧ F n ≤ 36
private theorem bound5 (η v : ℝ) : powerBound (fivePower η v) :=
  fun n => ⟨fivePower_nonneg η v n, fivePower_le η v n⟩
private theorem bound3 (η : ℝ) : powerBound (triplePower η) := triplePower_bounds η

private theorem summable_mass {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) {F : ℕ → ℝ} (hf : powerBound F) :
    Summable (fun k : ℕ => q^((k+1)^2-1)*F (k+1)) := by
  apply (summable_nat_add_iff 1).mp
  have hm := (summable_widthMoment 0 hq h1).mul_right 36
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hq _) (hf _).1) _ hm
  intro k
  simp only [pow_zero,one_mul]
  exact mul_le_mul_of_nonneg_left (hf _).2 (pow_nonneg hq _)

private theorem mass_diff_one {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) {F G : ℕ → ℝ}
    (hf : powerBound F) (hg : powerBound G) :
    normalizedMass q F - normalizedMass q G = F 1-G 1 +
      ∑' k : ℕ, q^((k+2)^2-1)*(F (k+2)-G (k+2)) := by
  have hs := (summable_mass hq h1 hf).sub (summable_mass hq h1 hg)
  unfold normalizedMass
  rw [← (summable_mass hq h1 hf).tsum_sub (summable_mass hq h1 hg),hs.tsum_eq_zero_add]
  simp [mul_sub, Nat.add_assoc]

private theorem diff_tail_summable {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) {F G : ℕ → ℝ}
    (hf : powerBound F) (hg : powerBound G) (k : ℕ) :
    Summable (fun j : ℕ => q^((j+k+1)^2-1)*(F (j+k+1)-G (j+k+1))) := by
  simpa only [mul_sub] using (summable_nat_add_iff k).mpr
    ((summable_mass hq h1 hf).sub (summable_mass hq h1 hg))

private theorem mass_diff_two {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) {F G : ℕ → ℝ}
    (hf : powerBound F) (hg : powerBound G) :
    normalizedMass q F - normalizedMass q G = F 1-G 1 + q^3*(F 2-G 2) +
      ∑' k : ℕ, q^((k+3)^2-1)*(F (k+3)-G (k+3)) := by
  rw [mass_diff_one hq h1 hf hg, (diff_tail_summable hq h1 hf hg 1).tsum_eq_zero_add]
  simp [add_assoc]

theorem centered_modal_gain (η : ℝ) (n : ℕ) :
    -(9*((n:ℝ)*η)^4) ≤ triplePower η n-fivePower η 0 n := by
  rcases neg_one_pow_eq_or ℝ n with hn|hn
  · have h := pow_le_pow_left₀ (abs_nonneg _) (five_deviation (n*η)) 2
    rw [sq_abs] at h
    simp only [triplePower, fivePower, hn, mul_zero, cos_zero, mul_one, sub_self]
    nlinarith only [h]
  · simp only [triplePower, fivePower, hn, mul_zero, cos_zero, mul_one]
    have h0 : 0 ≤ splitGain (n*η) := by unfold splitGain; positivity
    rw [splitGain_eq] at h0
    nlinarith only [h0,pow_nonneg (sq_nonneg ((n:ℝ)*η)) 2]

private theorem centered_first_gain (η : ℝ) :
    triplePower η 1 - fivePower η 0 1 = splitGain η := by
  rw [splitGain_eq]; simp [triplePower, fivePower]; ring

theorem centered_mass_gain {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) (η : ℝ) :
    splitGain η-9*widthR q*η^4 ≤ normalizedMass q (triplePower η)-
      normalizedMass q (fivePower η 0) := by
  rw [mass_diff_one hq h1 (bound3 η) (bound5 η 0),centered_first_gain]
  have hm := (summable_widthTerm hq h1).mul_left (-9*η^4)
  have hi := hm.tsum_le_tsum (g:=fun k : ℕ =>
    q^((k+2)^2-1)*(triplePower η (k+2)-fivePower η 0 (k+2))) (fun k => by
      have hb := mul_le_mul_of_nonneg_left (centered_modal_gain η (k+2)) (pow_nonneg hq ((k+2)^2-1))
      dsimp [widthTerm]
      nlinarith only [hb]) (diff_tail_summable hq h1 (bound3 η) (bound5 η 0) 1)
  rw [tsum_mul_left] at hi
  change (-9*η^4)*widthR q ≤ _ at hi
  linarith

/-- Motion of the singleton loses at worst a multiple of the scalar chord deficit. -/
theorem shifted_mode_loss {n : ℕ} (η v : ℝ) {b : ℝ} (hB : |five (n*η)| ≤ b) :
    -2*b*(n:ℝ)^2*(1-cos v) ≤ fivePower η 0 n-fivePower η v n := by
  have h1 : 0 ≤ 1-cos (n*v) := sub_nonneg.mpr (cos_le_one _)
  have hb : (-1:ℝ)^n*five (n*η) ≤ b := (le_abs_self _).trans (by simpa [abs_mul,abs_pow] using hB)
  have hc := one_sub_cos_nat_mul_le n v
  have h' := mul_le_mul hb hc h1 ((abs_nonneg _).trans hB)
  simp only [fivePower, mul_zero,cos_zero,mul_one]
  nlinarith only [h']

private theorem shifted_first (η v : ℝ) : fivePower η 0 1-fivePower η v 1 = 2*five η*(1-cos v) := by
  simp [fivePower]; ring

set_option maxHeartbeats 1200000 in
theorem shift_mass_comparison {q η : ℝ} (hq : 0 ≤ q) (h1 : q < 1)
    (hB : |five (2*η)| ≤ 1) (v : ℝ) :
    2*(five η-4*q^3-5*highTail 2 q)*(1-cos v) ≤ normalizedMass q (fivePower η 0)-
      normalizedMass q (fivePower η v) := by
  rw [mass_diff_two hq h1 (bound5 η 0) (bound5 η v),shifted_first]
  have hsecond := mul_le_mul_of_nonneg_left
    (shifted_mode_loss (n:=2) (b:=1) η v (by simpa using hB)) (pow_nonneg hq 3)
  have hs : Summable (tailTerm 2 q) :=
    (summable_nat_add_iff 1).mpr (summable_widthMoment 2 hq h1)
  have hm := hs.mul_left (-10*(1-cos v))
  have hi := hm.tsum_le_tsum (g:=fun k : ℕ =>
    q^((k+3)^2-1)*(fivePower η 0 (k+3)-fivePower η v (k+3))) (fun k => by
      calc
        _ = q^((k+3)^2-1)*(-2*5*((k+3:ℕ):ℝ)^2*(1-cos v)) := by unfold tailTerm; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (shifted_mode_loss (n:=k+3) η v (abs_five_le _))
          (pow_nonneg hq _)) (diff_tail_summable hq h1 (bound5 η 0) (bound5 η v) 2)
  rw [tsum_mul_left] at hi
  change (-10*(1-cos v))*highTail 2 q ≤ _ at hi
  norm_num only [Nat.cast_ofNat] at hsecond
  linarith only [hsecond,hi]

private theorem shift_bracket {q η : ℝ} (hq : 0 ≤ q) (hr : q ≤ 335/1000)
    (hη : 0 ≤ η) (he : η ≤ 44/100) : 26/100 < five η-4*q^3-5*highTail 2 q := by
  have hb := (abs_le.mp (five_deviation η)).1
  have hsq := pow_le_pow_left₀ hη he 2
  have hq3 := pow_le_pow_left₀ hq hr 3
  have ht := highTail_le (p:=2) hq hr (by norm_num) (by norm_num)
  norm_num [tailBound] at ht
  nlinarith only [hb,hsq,hq3,ht]

/-- Strict recentering whenever the new midpoint separation is not congruent
to the antipodal separation. -/
theorem small_angle_shift_strict {q η v : ℝ} (hq : 0 ≤ q) (hr : q ≤ 335/1000)
    (hη : 0 ≤ η) (he : η ≤ 44/100) (hv : cos v < 1) :
    normalizedMass q (fivePower η v) < normalizedMass q (fivePower η 0) := by
  have h1 := lt_of_le_of_lt hr (by norm_num : (335/1000:ℝ) < 1)
  have hB := five_double_unit hη (by linarith [pi_gt_three] : 2*η ≤ π/3)
  have hm := shift_mass_comparison hq h1 hB v
  have hb := shift_bracket hq hr hη he
  exact sub_pos.mp (lt_of_lt_of_le (mul_pos (by linarith) (sub_pos.mpr hv)) hm)

theorem small_angle_mass_lt {q η : ℝ} (hq : 0 ≤ q) (hr : q ≤ 335/1000)
    (hη : 0 < η) (he : η ≤ 44/100) (hR : widthR q < 615/1000) (v : ℝ) :
    normalizedMass q (fivePower η v) < normalizedMass q (triplePower η) := by
  have h1 := lt_of_le_of_lt hr (by norm_num : (335/1000:ℝ) < 1)
  have hB := five_double_unit hη.le (by linarith [pi_gt_three] : 2*η ≤ π/3)
  have hs := shift_mass_comparison hq h1 hB v
  have hc := centered_mass_gain hq h1 η
  have hd := broad_unequal_loss hη he hR
  have hb := shift_bracket hq hr hη.le he
  nlinarith only [hs,hc,hd,mul_nonneg (show 0 ≤ 2*(five η-4*q^3-5*highTail 2 q) by linarith)
    (sub_nonneg.mpr (cos_le_one v)),sq_nonneg η]

private theorem five_nonneg {η : ℝ} (hη : 0 ≤ η) (he : η ≤ π/5) : 0 ≤ five η := by
  have hm := strictAntiOn_cos.antitoneOn (show η ∈ Set.Icc 0 π from ⟨hη, by linarith [pi_pos]⟩)
    (show π/5 ∈ Set.Icc 0 π from ⟨by positivity,by linarith [pi_pos]⟩) he
  rw [cos_pi_div_five] at hm
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hg := sqrt_nonneg (5:ℝ)
  have h : 0 ≤ 4*cos η + √5-1 := by linarith
  rw [five,cos_two_mul]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hm) h,hs]

private theorem five_second_large {η : ℝ} (hη : 0 ≤ η) (he : η ≤ π/5) :
    |five (2*η)| ≤ 3 := by
  have hl := Real.cos_nonneg_of_mem_Icc (x:=2*η) ⟨by linarith [pi_pos],by linarith [pi_pos]⟩
  have hu := cos_le_one (2*η)
  rw [five, cos_two_mul (2*η),abs_le]
  constructor <;> nlinarith only [mul_nonneg hl (sub_nonneg.mpr hu),sq_nonneg (cos (2*η)-1/4),hu]

set_option maxHeartbeats 1200000 in
/-- Large-angle part of the narrow band. The first harmonic alone pays for
all the other harmonics of the shifted cell. -/
theorem large_angle_mass_lt {q η : ℝ} (hq : 0 ≤ q) (h1 : q < 1)
    (hl : 40/100 ≤ η) (he : η ≤ π/5)
    (hcap : 16*q^3+4*highTail 2 q < 405/1000) (v : ℝ) :
    normalizedMass q (fivePower η v) < normalizedMass q (triplePower η) := by
  have hη : 0 ≤ η := by linarith
  have hb := five_nonneg hη he
  have hh1 : splitGain η ≤ triplePower η 1-fivePower η v 1 := by
    have H := fivePower_le_square η v 1
    rw [Nat.cast_one,one_mul,abs_of_nonneg hb] at H
    rw [splitGain_eq]
    norm_num [triplePower] <;> linarith only [H]
  have hh2 : -16 ≤ triplePower η 2-fivePower η v 2 := by
    have H := fivePower_le_square η v 2
    have H2 := five_second_large hη he
    have sq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|five (2*η)|)
      (show 1+|five (2*η)| ≤ 4 by linarith) 2
    norm_num only [Nat.cast_ofNat] at H
    nlinarith only [H,sq,(triplePower_bounds η 2).1]
  have htail (k : ℕ) : -4*tailTerm 2 q k ≤
      q^((k+3)^2-1)*(triplePower η (k+3)-fivePower η v (k+3)) := by
    have hn : (3:ℝ) ≤ ((k+3 : ℕ):ℝ) := by exact_mod_cast (show 3 ≤ k+3 by omega)
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hn 2
    have hB : -4*((k+3:ℕ):ℝ)^2 ≤ triplePower η (k+3)-fivePower η v (k+3) := by
      nlinarith only [hsq, fivePower_le η v (k+3),(triplePower_bounds η (k+3)).1]
    calc
      _ = q^((k+3)^2-1)*(-4*((k+3:ℕ):ℝ)^2) := by unfold tailTerm; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (pow_nonneg hq _)
  have hs : Summable (tailTerm 2 q) :=
    (summable_nat_add_iff 1).mpr (summable_widthMoment 2 hq h1)
  have hu := (hs.mul_left (-4)).tsum_le_tsum htail
    (diff_tail_summable hq h1 (bound3 η) (bound5 η v) 2)
  rw [tsum_mul_left] at hu
  change -4*highTail 2 q ≤ _ at hu
  have hgap := narrow_first_mode_gap hl he
  apply sub_pos.mp
  rw [mass_diff_two hq h1 (bound3 η) (bound5 η v)]
  linarith only [hu,hh1,mul_le_mul_of_nonneg_left hh2 (pow_nonneg hq 3),hgap,hcap]

end GaussianChains.Strip
