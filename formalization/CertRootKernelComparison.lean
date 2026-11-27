import CertRootValue

/-! The two individual kernel comparisons used in the width-22 two-pair and
packed-face estimates. All three point enclosures include both infinite tails. -/
namespace GaussianChains.Root22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem quarter_check :
    (1/8:ℚ) < (kernelBox (1/4,1/4)).1 - (kernelBox (1/2,1/2)).2 := by decide +kernel

private theorem zero_check : (kernelBox (0,0)).2 ≤ 100001/100000 := by decide +kernel

theorem quarter_minus_half :
    (1/8:ℝ) < GaussianChains.kernel 22 (1/4) - GaussianChains.kernel 22 (1/2) := by
  have h₁ := (kernelBox_sound (d := (1/4,1/4)) (x := 1/4)
    (by norm_num [Encloses]) (by norm_num)).1
  have h₂ := (kernelBox_sound (d := (1/2,1/2)) (x := 1/2)
    (by norm_num [Encloses]) (by norm_num)).2
  have hq := (Rat.cast_lt (K := ℝ)).mpr quarter_check
  push_cast at hq
  exact hq.trans_le (sub_le_sub h₁ h₂)

theorem kernel_zero_upper : GaussianChains.kernel 22 0 ≤ 100001/100000 := by
  have h := (kernelBox_sound (d := (0,0)) (x := 0) (by norm_num [Encloses]) (by norm_num)).2
  have hq := (Rat.cast_le (K := ℝ)).mpr zero_check
  push_cast at hq
  exact h.trans hq

end GaussianChains.Root22
