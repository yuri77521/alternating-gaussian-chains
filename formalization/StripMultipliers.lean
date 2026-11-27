import ClustersTwo
import StripSplitGain
import Mathlib.Tactic.FinCases

/-! Harmonic multipliers for a maximal packed block of length one to four.
The index b=0,1,2,3 denotes length b+1. Even blocks carry a factor -i;
the table records its real sine multiplier. -/
noncomputable section
namespace GaussianChains.Strip
open Real

def blockMultiplier (b : Fin 4) (w : ℝ) : ℝ :=
  match b.val with
  | 0 => 1
  | 1 => 2*sin (w/2)
  | 2 => 2*cos w-1
  | _ => 4*cos w*sin (w/2)

private theorem cos_floor {η : ℝ} (hη : 0 ≤ η) (hmax : η ≤ π/5) : 4/5 ≤ cos η := by
  have hm := strictAntiOn_cos.antitoneOn
    (show η ∈ Set.Icc 0 π from ⟨hη, by linarith [pi_pos]⟩)
    (show π/5 ∈ Set.Icc 0 π from ⟨by positivity,by linarith [pi_pos]⟩) hmax
  rw [cos_pi_div_five] at hm
  have hs : (11/5:ℝ) ≤ √5 := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

theorem blockMultiplier_pos (b : Fin 4) {η : ℝ} (hη : 0 < η) (hmax : η ≤ π/5) :
    0 < blockMultiplier b η := by
  have hc := cos_floor hη.le hmax
  have hs : 0 < sin (η/2) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hcp : 0 < cos η := by linarith
  fin_cases b <;> simp [blockMultiplier] <;> first | positivity | linarith

theorem blockMultiplier_high (b : Fin 4) {η : ℝ} (hη : 0 < η) (hmax : η ≤ π/5)
    {n : ℕ} (hn : 3 ≤ n) :
    |blockMultiplier b ((n:ℝ)*η)| ≤ (5/3*(n:ℝ))*blockMultiplier b η := by
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hc := cos_floor hη.le hmax
  have hs : 0 < sin (η/2) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hsin := GaussianChains.abs_sin_nat_mul_le n (η/2)
  rw [abs_of_pos hs,← mul_div_assoc] at hsin
  fin_cases b
  · change |(1:ℝ)| ≤ _ * 1
    norm_num
    linarith
  · change |2*sin (↑n*η/2)| ≤ _*(2*sin (η/2))
    rw [abs_mul]; norm_num
    nlinarith only [hsin,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hs.le]
  · change |2*cos ((n:ℝ)*η)-1| ≤ _*(2*cos η-1)
    rw [abs_le]
    have hl : (3/5:ℝ) ≤ 2*cos η-1 := by linarith
    have hu := mul_le_mul hn' hl (by norm_num : (0:ℝ) ≤ 3/5) (Nat.cast_nonneg _)
    constructor <;> nlinarith only [hu,Real.cos_le_one ((n:ℝ)*η),Real.neg_one_le_cos ((n:ℝ)*η)]
  · change |4*cos ((n:ℝ)*η)*sin (↑n*η/2)| ≤ _*(4*cos η*sin (η/2))
    rw [abs_mul,abs_mul]; norm_num
    have ht := mul_le_mul (abs_cos_le_one ((n:ℝ)*η)) hsin (abs_nonneg _) (by norm_num)
    have hw := mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg (Nat.cast_nonneg n) hs.le)
    nlinarith only [ht,hw,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hs.le]

theorem blockMultiplier_second (b : Fin 4) {η : ℝ} (hη : 0 < η) (hmax : η ≤ π/5) :
    |blockMultiplier b (2*η)| ≤ 2*blockMultiplier b η := by
  have hc := cos_floor hη.le hmax
  have h1 := cos_le_one η
  have hs : 0 < sin (η/2) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hsin := GaussianChains.abs_sin_nat_mul_le 2 (η/2)
  norm_num [abs_of_pos hs] at hsin
  have hsin' : |sin (2*η/2)| ≤ 2*sin (η/2) := by convert hsin using 2 <;> ring
  rw [show 2*η/2=η by ring] at hsin'
  fin_cases b
  · norm_num [blockMultiplier]
  · change |2*sin (2*η/2)| ≤ 2*(2*sin (η/2))
    rw [abs_mul]; norm_num; linarith
  · change |2*cos (2*η)-1| ≤ 2*(2*cos η-1)
    rw [abs_le,cos_two_mul]
    constructor <;> nlinarith only [hc,h1,sq_nonneg (cos η-4/5),
      mul_nonneg (sub_nonneg.mpr h1) (by linarith : 0 ≤ cos η)]
  · change |4*cos (2*η)*sin (2*η/2)| ≤ 2*(4*cos η*sin (η/2))
    have hc2 : 0 ≤ cos (2*η) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos],by linarith [pi_pos]⟩
    have hle := strictAntiOn_cos.antitoneOn
      (show η ∈ Set.Icc 0 π from ⟨hη.le,by linarith [pi_pos]⟩)
      (show 2*η ∈ Set.Icc 0 π from ⟨by positivity,by linarith [pi_pos]⟩) (by linarith)
    rw [abs_mul,abs_mul,abs_of_nonneg hc2]
    norm_num
    nlinarith only [mul_le_mul hle hsin' (abs_nonneg _) (hc2.trans hle)]

end GaussianChains.Strip
