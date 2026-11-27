import ClusterSeriesCosine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.GCongr

/-! Exact 3+3 versus 5+1 multiplier comparison in the small-floor proof.
Angles below are angular gaps, not unit-period gaps. -/
noncomputable section
namespace GaussianChains.Strip
open Real

def triple (w : ℝ) := 2*cos w-1
def five (w : ℝ) := 1-2*cos w+2*cos (2*w)
def splitGain (w : ℝ) := 4*sin w^2*triple w^2

theorem splitGain_eq (w : ℝ) : splitGain w = 4*(triple w)^2-(1+five w)^2 := by
  dsimp [splitGain,triple,five]
  rw [cos_two_mul]
  linear_combination 4*(2*cos w-1)^2 * (sin_sq_add_cos_sq w)

theorem five_deviation (w : ℝ) : |five w-1| ≤ 3*w^2 := by
  have he : five w-1 = -4*sin (3*w/2)*sin (w/2) := by
    dsimp [five]
    have h := cos_sub_cos (2*w) w
    rw [show (2*w+w)/2 = 3*w/2 by ring,show (2*w-w)/2 = w/2 by ring] at h
    linarith
  rw [he,abs_mul,abs_mul]
  norm_num
  have h := mul_le_mul (Real.abs_sin_le_abs (x:=3*w/2)) (Real.abs_sin_le_abs (x:=w/2))
    (abs_nonneg _) (abs_nonneg _)
  simp [abs_mul,abs_div] at h
  nlinarith only [h,sq_abs w]

theorem five_double_unit {w : ℝ} (hw : 0 ≤ w) (hpi : 2*w ≤ π/3) :
    |five (2*w)| ≤ 1 := by
  have h1 : cos (2*w) ≤ 1 := cos_le_one _
  have h2 : 1/2 ≤ cos (2*w) := by
    rw [← cos_pi_div_three]
    apply strictAntiOn_cos.antitoneOn ⟨by positivity,by linarith [pi_pos]⟩
      ⟨by positivity,by linarith [pi_pos]⟩ hpi
  rw [five, cos_two_mul (2*w),abs_le]
  constructor <;> nlinarith only [mul_nonneg (by linarith : 0 ≤ cos (2*w))
      (by linarith : 0 ≤ 2*cos (2*w)-1),
    mul_nonneg (by linarith : 0 ≤ 2*cos (2*w)+1) (sub_nonneg.mpr h1)]

private theorem gain_lower {w e : ℝ} (hw : 0 ≤ w) (he : w ≤ e) (he' : e ≤ 1) :
    (4*(1-e^2/6)^2*(1-e^2)^2)*w^2 ≤ splitGain w := by
  have hpow := pow_le_pow_left₀ hw he 2
  have h0 : 0 ≤ e := hw.trans he
  have hE := pow_le_pow_left₀ h0 he' 2
  have hs := (abs_le.mp (ClusterSeries.sin_linear_bound w)).1
  rw [abs_of_nonneg hw] at hs
  have hs' : (1-e^2/6)*w ≤ sin w := by
    nlinarith only [hs,mul_nonneg hw (sub_nonneg.mpr hpow)]
  have hc : 1-e^2 ≤ triple w := by
    dsimp [triple]
    nlinarith only [one_sub_sq_div_two_le_cos (x:=w),hpow]
  have hs2 := pow_le_pow_left₀ (mul_nonneg (by nlinarith) hw) hs' 2
  have hc2 := pow_le_pow_left₀ (by nlinarith) hc 2
  dsimp [splitGain]
  nlinarith only [mul_le_mul hs2 hc2 (sq_nonneg _) (sq_nonneg _)]

theorem broad_unequal_loss {w R : ℝ} (hw : 0 < w) (he : w ≤ 44/100) (hR : R < 615/1000) :
    (136/100)*w^2 < splitGain w-9*R*w^4 := by
  have h := gain_lower hw.le he (by norm_num)
  have hpow := pow_le_pow_left₀ hw.le he 2
  have h4 := mul_le_mul_of_nonneg_right hpow (sq_nonneg w)
  have hR' := mul_lt_mul_of_pos_right hR (by positivity : 0 < w^4)
  nlinarith only [h,h4,hR',sq_pos_of_pos hw]

theorem narrow_unequal_loss {w R : ℝ} (hw : 0 < w) (he : w ≤ 40/100) (hR : R < 41/100) :
    0 < splitGain w-9*R*w^4 := by
  have h := gain_lower hw.le he (by norm_num)
  have hpow := pow_le_pow_left₀ hw.le he 2
  have h4 := mul_le_mul_of_nonneg_right hpow (sq_nonneg w)
  have hR' := mul_lt_mul_of_pos_right hR (by positivity : 0 < w^4)
  nlinarith only [h,h4,hR',sq_pos_of_pos hw]

private def gainPolynomial (x : ℝ) := 4*(1-x^2)*(2*x-1)^2

private theorem secant_gain {x : ℝ} (hl : 4/5 ≤ x) (hr : x ≤ 461/500) :
    405/1000 < gainPolynomial x := by
  let a : ℝ := 4/5
  let b : ℝ := 461/500
  let Q := 16*x^2+16*(a+b-1)*x+16*(a^2+a*b+b^2)-16*(a+b)-12
  have hQ : 0 ≤ Q := by dsimp [Q,a,b]; nlinarith only [hl,sq_nonneg x]
  have hid : (b-a)*gainPolynomial x =
      (b-x)*gainPolynomial a + (x-a)*gainPolynomial b + (b-a)*((x-a)*(b-x))*Q := by
    dsimp [Q,gainPolynomial]; ring
  have hx₁ : 0 ≤ b-x := sub_nonneg.mpr hr
  have hx₂ : 0 ≤ x-a := sub_nonneg.mpr hl
  have hc := mul_nonneg (mul_nonneg (by norm_num [a,b] : 0 ≤ b-a) (mul_nonneg hx₂ hx₁)) hQ
  have ha : 41/100 < gainPolynomial a := by norm_num [a,gainPolynomial]
  have hb : 41/100 < gainPolynomial b := by norm_num [b,gainPolynomial]
  have hlin := add_le_add (mul_le_mul_of_nonneg_left ha.le hx₁) (mul_le_mul_of_nonneg_left hb.le hx₂)
  dsimp [a,b] at hid hc hlin
  nlinarith only [hid,hc,hlin]

theorem narrow_first_mode_gap {w : ℝ} (hl : 40/100 ≤ w) (hr : w ≤ π/5) :
    405/1000 < splitGain w := by
  have h₀ : 0 ≤ w := by linarith
  have hπ : w ≤ π := by linarith [pi_pos]
  have hx₁ : 4/5 ≤ cos w := by
    have hm := strictAntiOn_cos.antitoneOn ⟨h₀,hπ⟩
      (show π/5 ∈ Set.Icc 0 π from ⟨by positivity,by linarith [pi_pos]⟩) hr
    rw [cos_pi_div_five] at hm
    have hs : (11/5:ℝ) ≤ √5 := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith
  have hx₂ : cos w ≤ 461/500 := by
    have hm := strictAntiOn_cos.antitoneOn
      (show (40/100:ℝ) ∈ Set.Icc 0 π from ⟨by norm_num,by linarith [pi_gt_three]⟩) ⟨h₀,hπ⟩ hl
    have hu := (abs_le.mp (ClusterSeries.cos_second_bound (40/100))).2
    linarith
  rw [splitGain,triple,show sin w ^2 = 1-cos w^2 by linarith [sin_sq_add_cos_sq w]]
  exact secant_gain hx₁ hx₂

end GaussianChains.Strip
