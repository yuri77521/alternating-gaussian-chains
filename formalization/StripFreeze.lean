import ChainFourier
import Mathlib.Analysis.Complex.Basic

/-! Freezing the Fourier potential at a global minimizer. The positive quadratic
remainder in the score implies an exact necessary comparison for any feasible
block translation, on the whole finite-energy sequence space. -/
noncomputable section
namespace GaussianChains.Strip
open scoped ComplexConjugate

def weight (s : ℝ) (k : ℕ) := Real.exp (-(Real.pi^2)/s)^((k+1)^2)

def frozenTerm {N : ℕ} (s : ℝ) (x y : Fin N → ℝ) (k : ℕ) : ℝ :=
  weight s k * (conj (structureFactor x (k+1)) * structureFactor y (k+1)).re

theorem frozen_summable {N : ℕ} {s : ℝ} (hs : 0 < s) (x y : Fin N → ℝ) :
    Summable (frozenTerm s x y) := by
  have bound (a b : ℂ) : |(conj a*b).re| ≤ (‖a‖^2+‖b‖^2)/2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    nlinarith only [sq_nonneg (‖a‖-‖b‖)]
  refine Summable.of_norm_bounded (((fourier_summable x hs).add (fourier_summable y hs)).div_const 2) ?_
  intro k
  change |weight s k * _| ≤ (_ + _)/2
  rw [abs_mul,abs_of_nonneg (show 0 ≤ weight s k by unfold weight; positivity)]
  have h := mul_le_mul_of_nonneg_left (bound (structureFactor x (k+1)) (structureFactor y (k+1)))
    (show 0 ≤ weight s k by unfold weight; positivity)
  dsimp [weight] at h ⊢
  linarith only [h]

/-- The reference's self-overlap equals its ordinary Fourier score. -/
theorem frozen_self {N : ℕ} (s : ℝ) (x : Fin N → ℝ) (k : ℕ) :
    frozenTerm s x x k = weight s k * ‖structureFactor x (k+1)‖^2 := by
  rw [frozenTerm,mul_comm (conj _),Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]

theorem frozen_at_minimizer (m : ℕ) (hm : 0<m) {s : ℝ} (hs : 0<s)
    (x y : Fin (2*m) → ℝ) (hE : imageEnergy s x ≤ imageEnergy s y) :
    (∑' k, frozenTerm s x y k) ≤ ∑' k, frozenTerm s x x k := by
  let score (u : Fin (2*m) → ℝ) (k : ℕ) := weight s k * ‖structureFactor u (k+1)‖^2
  have trans (a b : ℂ) : 2*(conj a*b).re ≤ ‖a‖^2+‖b‖^2 := by
    have hb := (le_abs_self ((conj a*b).re)).trans (Complex.abs_re_le_norm _)
    rw [norm_mul,Complex.norm_conj] at hb
    nlinarith only [hb,sq_nonneg (‖a‖-‖b‖)]
  have hmodes : ∀ k, 2*frozenTerm s x y k ≤ score x k+score y k := by
    intro k
    dsimp only [score,frozenTerm]
    have h := mul_le_mul_of_nonneg_left (trans (structureFactor x (k+1)) (structureFactor y (k+1)))
      (show 0 ≤ weight s k by unfold weight; positivity)
    linarith only [h]
  have hsum := ((frozen_summable hs x y).mul_left 2).tsum_le_tsum hmodes
    ((fourier_summable x hs).add (fourier_summable y hs))
  have hS (u : Fin (2*m) → ℝ) : Summable (score u) := fourier_summable u hs
  rw [tsum_mul_left, (hS x).tsum_add (hS y)] at hsum
  rw [imageEnergy_fourier m hs x,imageEnergy_fourier m hs y,sub_le_sub_iff_left] at hE
  have hpos : 0 < 2*Real.sqrt (Real.pi/s)/((2*m:ℕ):ℝ) := by positivity
  have hscore := (mul_le_mul_iff_right₀ hpos).mp hE
  change (∑' k, score y k) ≤ ∑' k, score x k at hscore
  simp_rw [frozen_self]
  exact (by linarith only [hsum,hscore] :
    (∑' k, frozenTerm s x y k) ≤ ∑' k, score x k)

end GaussianChains.Strip
