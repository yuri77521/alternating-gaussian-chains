import PackedFaceCurvature
import PackedFaceSlopesTransition

/-! The signed-displacement curvature along the centered branch changes sign at
the actual critical floor, on the full range of Theorem 3. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set

theorem centered_curvature_signs {s h : ℝ} (hs : 0 < s)
    (hQ : Real.exp (-(Real.pi^2)/s) ≤ faceQ) (hh : 0 < h) (h6 : h ≤ 1/6) :
    let r := criticalFloor false (Real.exp (-(Real.pi^2)/s))
    let κ := deriv (deriv (fun t => imageEnergy s (sites h t))) 0
    (h < r → 0 < κ) ∧ (h = r → κ = 0) ∧ (r < h → κ < 0) := by
  dsimp only
  let q := Real.exp (-(Real.pi^2)/s)
  have hq : 0 < q := Real.exp_pos _
  have hr := criticalFloor_spec false hq hQ
  have hm : StrictAntiOn (floorSlope false q) (Icc (1/8) (1/6)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_floorSlope false hq.le hQ)
      (by rw [interior_Icc]; exact fun _ hz => floorSlope_deriv_neg false hq hQ hz)
  have link (u : ℝ) : floorSlope false q u = phiD q u 0 := by
    simp [floorSlope,endpointZ,phiD_eq_endpointSlope]
  rw [centered_curvature hs hQ]
  change (h < criticalFloor false q → 0 < _ * phiD q h 0) ∧
    (h = criticalFloor false q → _ * phiD q h 0 = 0) ∧
    (criticalFloor false q < h → _ * phiD q h 0 < 0)
  have hp : 0 < (4 * Real.sqrt (Real.pi/s) * q / 6) * (2 * Real.pi)^2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    apply mul_pos hp
    rcases le_total h (1/8) with h8 | h8
    · exact phiD_pos_small_floor hq.le hQ hh.le h8 (by constructor <;> norm_num)
    · have H := hm ⟨h8,h6⟩ (Ioo_subset_Icc_self hr.1) hc
      simpa only [hr.2.1,link] using H
  · rintro rfl
    rw [← link, hr.2.1, mul_zero]
  · intro hc
    apply mul_neg_of_pos_of_neg hp
    have H := hm (Ioo_subset_Icc_self hr.1) ⟨hr.1.1.le.trans hc.le,h6⟩ hc
    simpa only [hr.2.1,link] using H

end GaussianChains.PackedFace
