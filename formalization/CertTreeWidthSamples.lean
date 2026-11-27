import CertTreeFourierCaps
import CertRootExp

/-! Exponential boxes for the width-strip anchor and endpoint nomes, with
outward rational square-root bounds for the amplitudes. -/
namespace GaussianChains.WidthBounds
open FourierBounds

def piLo : ℚ := 3.14159265358979323846
def piHi : ℚ := 3.14159265358979323847

theorem pi_left : (piLo:ℝ) ≤ Real.pi := by
  simpa [piLo] using Real.pi_gt_d20.le

theorem pi_right : Real.pi ≤ (piHi:ℝ) := by
  simpa [piHi] using Real.pi_lt_d20.le

structure Sample where
  width : ℚ
  low : ℚ
  high : ℚ
  factor : ℚ

def Sample.Valid (d : Sample) : Prop :=
  0 < d.width ∧ 0 ≤ d.low ∧ d.high < 1 ∧ 0 ≤ d.factor ∧
  piHi^2/d.width ≤ 600 ∧ piHi ≤ d.factor^2*d.width ∧
  d.low ≤ (CertExp.negExpRange (piLo^2/d.width) (piHi^2/d.width)).1 ∧
  (CertExp.negExpRange (piLo^2/d.width) (piHi^2/d.width)).2 ≤ d.high

instance (d : Sample) : Decidable d.Valid := by unfold Sample.Valid; infer_instance

theorem sample_sound (d : Sample) (hd : d.Valid) :
    0 < (d.width:ℝ) ∧ (d.low:ℝ) ≤ nome d.width ∧ nome d.width ≤ (d.high:ℝ) ∧
    scale d.width ≤ (d.factor:ℝ) := by
  obtain ⟨hs,_,_,hfac,hmax,hsq,hLo,hHi⟩ := hd
  have hs₀ : (0:ℝ) < d.width := by exact_mod_cast hs
  have hPi : (0:ℝ) ≤ piLo := by norm_num [piLo]
  have hl : ((piLo^2/d.width : ℚ):ℝ) ≤ Real.pi^2 / d.width := by
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hPi pi_left 2) hs₀.le
  have hu : Real.pi^2 / d.width ≤ ((piHi^2/d.width : ℚ):ℝ) := by
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ Real.pi_pos.le pi_right 2) hs₀.le
  have hz : 0 ≤ piLo^2/d.width := div_nonneg (sq_nonneg _) hs.le
  obtain ⟨hlo,hhi⟩ := CertExp.negExpRange_sound hz hmax hl hu
  refine ⟨hs₀, ?_, ?_, ?_⟩
  · rw [nome, neg_div]
    exact (Rat.cast_le.mpr hLo).trans hlo
  · rw [nome, neg_div]
    exact hhi.trans (Rat.cast_le.mpr hHi)
  · refine Real.sqrt_le_iff.mpr ⟨by exact_mod_cast hfac, (div_le_iff₀ hs₀).mpr ?_⟩
    exact pi_right.trans (by exact_mod_cast hsq)

private def sample (w : ℚ) (q₀ q₁ c : ℕ) : Sample := ⟨w, q₀/10^16, q₁/10^16, c/10^16⟩
def w799 := sample (799/100) 2907636311708407 2907636311708408 6270490968904374
def w800 := sample 8 2912129332140208 2912129332140209 6266570686577502
def w801 := sample (801/100) 2916618050886468 2916618050886469 6262657747896520
def w825 := sample (33/4) 3023059530155700 3023059530155701 6170892233105644
def w850 := sample (17/2) 3131321636314084 3131321636314085 6079466553213747
def w875 := sample (35/4) 3236946037568731 3236946037568732 5991987653610963
def w900 := sample 9 3339971859861317 3339971859861318 5908179503018387

set_option maxRecDepth 20000 in
theorem w799_valid : w799.Valid := by decide +kernel

set_option maxRecDepth 20000 in
theorem w800_valid : w800.Valid := by decide +kernel

set_option maxRecDepth 20000 in
theorem w801_valid : w801.Valid := by decide +kernel

set_option maxRecDepth 20000 in
theorem w825_valid : w825.Valid := by decide +kernel

set_option maxRecDepth 20000 in
theorem w850_valid : w850.Valid := by decide +kernel

set_option maxRecDepth 20000 in
theorem w875_valid : w875.Valid := by decide +kernel

set_option maxRecDepth 20000 in
theorem w900_valid : w900.Valid := by decide +kernel

end GaussianChains.WidthBounds
