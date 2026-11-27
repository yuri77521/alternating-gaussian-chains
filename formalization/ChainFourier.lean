import ChainEnergy
import KernelFourier
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-! The structure factor of an alternating cell. All frequency series below
start at mode one and converge at every positive Gaussian width. -/

noncomputable section

namespace GaussianChains

open Real

/-- Complex amplitude at mode n, with coordinates measured in units of the period. -/
def structureFactor {N : ℕ} (x : Fin N → ℝ) (n : ℕ) : ℂ :=
  ∑ j, (charge j : ℂ) * Complex.exp (((2 * π * (n : ℝ) * x j : ℝ) : ℂ) * Complex.I)

theorem charge_sum_even (m : ℕ) : (∑ i : Fin (2*m), charge i) = 0 := by
  have h (k : ℕ) : ∑ i ∈ Finset.range (2*k), (-1 : ℝ)^i = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
      ring
  simpa [charge, Fin.sum_univ_eq_sum_range] using h m

/-- Electroneutrality removes the zero Fourier mode, even at collisions. -/
theorem structureFactor_zero (m : ℕ) (x : Fin (2*m) → ℝ) : structureFactor x 0 = 0 := by
  simpa [structureFactor] using congrArg Complex.ofReal (charge_sum_even m)

theorem pairCos_eq_norm_structureFactor {N : ℕ} (x : Fin N → ℝ) (n : ℕ) :
    (∑ i, ∑ j, charge i * charge j * cos (2 * π * n * (x j - x i))) =
      ‖structureFactor x n‖ ^ 2 := by
  let angle (i : Fin N) := 2 * π * (n : ℝ) * x i
  let C (i : Fin N) := charge i * cos (angle i)
  let S (i : Fin N) := charge i * sin (angle i)
  have hpair (i j : Fin N) :
      charge i * charge j * cos (2 * π * n * (x j - x i)) = C i * C j + S i * S j := by
    change _ = charge i * cos (angle i) * (charge j * cos (angle j)) +
      charge i * sin (angle i) * (charge j * sin (angle j))
    rw [mul_sub, Real.cos_sub]
    dsimp [angle]
    ring
  have hre : (structureFactor x n).re = ∑ i, C i := by
    simp only [structureFactor, Complex.re_sum, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, C, angle]
  have him : (structureFactor x n).im = ∑ i, S i := by
    simp only [structureFactor, Complex.im_sum, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, S, angle]
  simp_rw [hpair, Finset.sum_add_distrib]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact congrArg₂ (· + ·) Finset.sum_comm Finset.sum_comm

private def mode (s d : ℝ) (k : ℕ) : ℝ :=
  exp (-(π^2)/s)^((k+1)^2) * cos (2 * π * ((k+1:ℕ):ℝ) * d)

private theorem signed_modes_hasSum {N : ℕ} (x : Fin N → ℝ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => exp (-(π^2)/s)^((k+1)^2) * ‖structureFactor x (k+1)‖^2)
      (∑ i, ∑ j, charge i * charge j * ∑' k, mode s (x j - x i) k) := by
  have hp : HasSum (fun k : ℕ => ∑ i, ∑ j, charge i * charge j * mode s (x j - x i) k)
      (∑ i, ∑ j, charge i * charge j * ∑' k, mode s (x j - x i) k) := by
    apply hasSum_sum
    intro i _
    apply hasSum_sum
    intro j _
    exact ((summable_cos_modes hs (x j - x i)).hasSum).mul_left _
  apply hp.congr_fun
  intro k
  rw [← pairCos_eq_norm_structureFactor]
  simp only [Finset.mul_sum, mode]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fourier_summable {N : ℕ} (x : Fin N → ℝ) {s : ℝ} (hs : 0 < s) :
    Summable (fun k : ℕ => exp (-(π^2)/s)^((k+1)^2) * ‖structureFactor x (k+1)‖^2) :=
  (signed_modes_hasSum x hs).summable

/-- Equation (2) at every width. No gap floor is needed for the identity. -/
theorem imageEnergy_fourier (m : ℕ) {s : ℝ} (hs : 0 < s) (x : Fin (2*m) → ℝ) :
    imageEnergy s x =
      1 - 2 * sqrt (π/s) / ((2*m : ℕ) : ℝ) *
        ∑' k : ℕ, exp (-(π^2)/s)^((k+1)^2) * ‖structureFactor x (k+1)‖^2 := by
  let c := sqrt (π/s)
  let f (i j : Fin (2*m)) := ∑' k, mode s (x j - x i) k
  have hK (i j : Fin (2*m)) : kernel s (x j-x i) = c * (1 + 2*f i j) :=
    kernel_fourier hs _
  have pair (i j : Fin (2*m)) : charge i * charge j * kernel s (x j-x i) =
      c * (charge i * charge j) + 2*c*(charge i*charge j*f i j) := by rw [hK]; ring
  have hzero : (∑ i : Fin (2*m), ∑ j : Fin (2*m), charge i * charge j) = 0 := by
    simp only [← Finset.mul_sum, charge_sum_even, mul_zero, Finset.sum_const_zero]
  have total : (∑ i, ∑ j, charge i * charge j * kernel s (x j - x i)) =
      c * (∑ i : Fin (2*m), ∑ j : Fin (2*m), charge i * charge j) +
      (2*c) * (∑ i, ∑ j, charge i * charge j * f i j) := by
    simp_rw [pair, Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
  rw [imageEnergy, total, hzero, mul_zero, zero_add, (signed_modes_hasSum x hs).tsum_eq]
  dsimp [f, c]
  ring

/-- The ordered, central-self-deleted sum in physical units equals the full
positive-mode expression after exactly the substitutions in §2. -/
theorem physicalEnergy_fourier (m : ℕ) (hm : 0 < m) (α L : ℝ) (hα : 0 < α) (hL : 0 < L)
    (X : Fin (2*m) → ℝ) :
    let s := α * L ^ 2
    physicalEnergy α L X =
      1 - 2 * sqrt (π/s) / ((2*m : ℕ) : ℝ) *
        ∑' k : ℕ, exp (-(π^2)/s)^((k+1)^2) *
          ‖structureFactor (fun i => X i / L) (k+1)‖^2 := by
  dsimp only
  rw [physicalEnergy_eq_imageEnergy (by omega) α L hα hL]
  exact imageEnergy_fourier m (by positivity) _

#print axioms imageEnergy_fourier
#print axioms physicalEnergy_fourier

end GaussianChains
