import PackedFaceSlopes
import PackedFaceGeometry
import PackedFaceBoundsSigns

/-! Equality of the two formulas for the slope and the left boundary signs. -/
namespace GaussianChains.PackedFace
open Polynomial Polynomial.Chebyshev

theorem phiD_eq_endpointSlope (q h y : ℝ) :
    phiD q h y = endpointSlope q (Real.cos (2*Real.pi*h)) (1-y) := by
  apply tsum_congr
  intro k
  unfold phiModeD amplitude endpointMode modeT modeU
  rw [T_derivative_eq_U, eval_mul, eval_intCast, Int.cast_natCast]
  rw [pow_succ (-1:ℝ) (k+1)]
  ring

theorem outer_abscissa (h : ℝ) :
    1 - coord (bound h) =
      3 * Real.cos (2*Real.pi*h) - 4 * Real.cos (2*Real.pi*h)^3 := by
  unfold coord bound
  rw [show 2*Real.pi*(1/2-3*h) = Real.pi-3*(2*Real.pi*h) by ring,
    Real.cos_pi_sub,Real.cos_three_mul]
  ring

theorem inner_endpoint_slopes_pos {q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) :
    0 < endpointSlope q (Real.cos (2*Real.pi*(1/8))) 1 ∧
    0 < endpointSlope q (Real.cos (2*Real.pi*(1/8))) (1-coord (bound (1/8))) := by
  constructor
  · simpa only [phiD_eq_endpointSlope,sub_zero] using
      phiD_pos_small_floor hq hQ (by norm_num : (0:ℝ) ≤ 1/8) le_rfl
        (show (0:ℝ) ∈ Set.Icc 0 2 by constructor <;> norm_num)
  · rw [← phiD_eq_endpointSlope]
    apply phiD_pos_small_floor hq hQ (by norm_num) le_rfl
    unfold coord
    constructor <;> linarith [Real.neg_one_le_cos (2*Real.pi*bound (1/8)),
      Real.cos_le_one (2*Real.pi*bound (1/8))]

end GaussianChains.PackedFace
