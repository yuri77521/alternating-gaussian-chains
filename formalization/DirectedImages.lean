import ChainScore
import ChainFourier

/-! Fubini for the literal signed sum on both labels and the integer index of
the periodic copy, prior to any cancellation or regrouping. -/
noncomputable section
namespace GaussianChains
open Real

def directedImage {N : ℕ} (α L : ℝ) (X : Fin N → ℝ)
    (p : (Fin N × Fin N) × ℤ) : ℝ :=
  charge p.1.1 * charge p.1.2 * primedImage α L X p.1.1 p.1.2 p.2

theorem physicalEnergy_eq_product_tsum {N : ℕ} (α L : ℝ) (hα : 0 < α) (hL : 0 < L)
    (X : Fin N → ℝ) :
    physicalEnergy α L X = -(∑' p, directedImage α L X p)/(N : ℝ) := by
  have h : Summable (directedImage α L X) :=
    (summable_abs_directed_images α L hα hL X).of_abs
  rw [h.tsum_prod, tsum_fintype, Fintype.sum_prod_type]
  simp only [directedImage, tsum_mul_left, physicalEnergy]

theorem product_tsum_fourier (m : ℕ) (hm : 0 < m) (α L : ℝ) (hα : 0 < α) (hL : 0 < L)
    (X : Fin (2*m) → ℝ) :
    let s := α * L ^ 2;
    -(∑' p, directedImage α L X p)/((2*m : ℕ) : ℝ) =
      1 - 2*sqrt (π/s)/((2*m : ℕ) : ℝ) *
        ∑' k : ℕ, exp (-(π^2)/s)^((k+1)^2) *
          ‖structureFactor (fun i => X i/L) (k+1)‖^2 := by
  dsimp only
  rw [← physicalEnergy_eq_product_tsum α L hα hL X]
  exact physicalEnergy_fourier m hm α L hα hL X

end GaussianChains
