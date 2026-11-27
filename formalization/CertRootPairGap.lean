import CertRootHalfPeriod
import CertRootKernelComparison

noncomputable section
namespace GaussianChains.Root22
open Set

/-- The gap from the antipodal pair energy is controlled on the entire short arc. -/
theorem kernel_quadratic_gap {r : ℝ} (hr : r ∈ Icc (0:ℝ) (1/2)) :
    (1/2-r)^2/2 ≤ GaussianChains.kernel 22 r - GaussianChains.kernel 22 (1/2) := by
  by_cases h : 1/4 ≤ r
  · let f (x : ℝ) := GaussianChains.kernel 22 x - (x-1/2)^2/2
    have hd (x : ℝ) : HasDerivAt f (derivKernel x-(x-1/2)) x := by
      convert (hasDerivAt_kernel22 x).sub ((((hasDerivAt_id x).sub_const (1/2)).pow 2).div_const 2) using 1 <;> simp [f] <;> ring
    have ha := antitoneOn_interval_of_slope hd (a := 1/4) (b := 1/2) (fun z hz => sub_nonpos.mpr (derivKernel_le_displacement hz))
    have hb := ha (show r ∈ Icc (1/4:ℝ) (1/2) from ⟨h,hr.2⟩)
      (show (1/2:ℝ) ∈ Icc (1/4:ℝ) (1/2) by norm_num) hr.2
    dsimp [f] at hb
    nlinarith
  · have hm := kernel_antitoneOn_half hr (show (1/4:ℝ) ∈ Icc (0:ℝ) (1/2) by norm_num) (by linarith)
    have hv := pow_le_pow_left₀ (show 0 ≤ 1/2-r by linarith [hr.2]) (show 1/2-r ≤ 1/2 by linarith [hr.1]) 2
    linarith [quarter_minus_half]

end GaussianChains.Root22
