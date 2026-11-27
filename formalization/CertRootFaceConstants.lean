import CertRootValue

/-! Checked bounds for the antipodal auxiliary energy and the packed triple's internal cost. -/
namespace GaussianChains.Root22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem packed_constants_checked :
    (0.669391180769582:ℚ) < 1 + ((kernelBox (1/2,1/2)).1 - (kernelBox (0,0)).2)/3 ∧
    (kernelBox (2/1000,2/1000)).2 - 2*(kernelBox (1/1000,1/1000)).1 +
      (kernelBox (0,0)).2 < 0 ∧ (kernelBox (0,0)).2 ≤ 1.00001 := by decide +kernel

private theorem literalKernel (q : ℚ) (hq : |(q:ℝ)| ≤ 1) :
    Encloses (kernelBox (q,q)) (kernel 22 (q:ℝ)) :=
  kernelBox_sound ⟨le_rfl,le_rfl⟩ hq

theorem packed_numeric_bounds :
    0.669391180769582 < 1 + (kernel 22 (1/2)-kernel 22 0)/3 ∧
    kernel 22 (2/1000) - 2*kernel 22 (1/1000) + kernel 22 0 < 0 ∧ kernel 22 0 ≤ 1.00001 := by
  have h0 := (literalKernel 0 (by norm_num)).2
  have h1 := (literalKernel (1/1000) (by norm_num)).1
  have h2 := (literalKernel (2/1000) (by norm_num)).2
  have hh := (literalKernel (1/2) (by norm_num)).1
  push_cast at h0 h1 h2 hh
  obtain ⟨a,b,c⟩ := packed_constants_checked
  have a' : (0.669391180769582:ℝ) <
      1+(((kernelBox (1/2,1/2)).1:ℝ)-(kernelBox (0,0)).2)/3 := by
    simpa only [Rat.cast_ofScientific, Rat.cast_add, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr a
  have b' : ((kernelBox (2/1000,2/1000)).2:ℝ) - 2*(kernelBox (1/1000,1/1000)).1 +
      (kernelBox (0,0)).2 < 0 := by exact_mod_cast b
  have c' : ((kernelBox (0,0)).2:ℝ) ≤ 1.00001 := by
    simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).mpr c
  refine ⟨by linarith, ?_, h0.trans c'⟩
  linarith

/-- Lower bound for the two effective opposite charges at antipodal separation. -/
theorem antipodal_auxiliary_lower :
    0.669391180769582 < 1 + (kernel 22 (1/2)-kernel 22 0)/3 := packed_numeric_bounds.1

end GaussianChains.Root22
