import PackedFaceBoundsComplex
import PackedFaceSlopes

namespace GaussianChains.PackedFace
open Polynomial.Chebyshev

theorem ofReal_endpointMode (n : ℕ) (q x z : ℝ) :
    ((endpointMode n q x z : ℝ) : ℂ) = complexSlopeMode n q x z := by
  simp only [endpointMode, modeT, modeU, complexSlopeMode, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, complex_ofReal_eval_T, complex_ofReal_eval_U]

theorem ofReal_endpointSlope (q x z : ℝ) :
    ((endpointSlope q x z : ℝ) : ℂ) = ∑' k : ℕ, complexSlopeMode (k+1) q x z := by
  simp only [endpointSlope, Complex.ofReal_tsum, ofReal_endpointMode]

end GaussianChains.PackedFace
