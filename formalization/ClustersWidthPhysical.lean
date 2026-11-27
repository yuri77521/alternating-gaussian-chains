import ClustersWidthKernel
import ChainFourier

/-! Normalized angular score and physical energy in the locking proof. -/

noncomputable section
open Real
namespace GaussianChains

theorem kernel_eq_angularK {s : ℝ} (hs : 0 < s) (d : ℝ) :
    kernel s d = sqrt (π/s) * (1 + 2 * exp (-(π^2)/s) *
      angularK (exp (-(π^2)/s)) (2*π*d)) := by
  let q := exp (-(π^2)/s)
  let f (k : ℕ) := q^((k+1)^2) * cos (2*π*((k+1 : ℕ) : ℝ)*d)
  have hf : Summable f := summable_cos_modes hs d
  have htail (k : ℕ) : f (k+1) =
      q * (q^((k+2)^2-1) * cos (((k+2:ℕ):ℝ)*(2*π*d))) := by
    have hp : q^((k+2)^2-1) * q = q^((k+2)^2) := by
      rw [← pow_succ, Nat.sub_add_cancel (show 0 < (k+2)^2 by positivity)]
    rw [show q * (q^((k+2)^2-1) * cos (((k+2:ℕ):ℝ)*(2*π*d))) =
      (q^((k+2)^2-1) * q) * cos (((k+2:ℕ):ℝ)*(2*π*d)) by ring, hp]
    dsimp [f]
    congr 2 <;> push_cast <;> ring
  rw [kernel_fourier hs, angularK_eq]
  change sqrt (π/s) * (1 + 2*(∑' k, f k)) = _
  rw [hf.tsum_eq_zero_add]
  simp_rw [htail]
  rw [tsum_mul_left]
  have hz : f 0 = q * cos (2*π*d) := by simp [f]
  rw [hz]
  dsimp [q]
  ring

/-- Labels in period-one coordinates; the arguments of K are angular differences. -/
def angularScore {N : ℕ} (q : ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, charge i * charge j * angularK q (2*π*(x j - x i))

theorem imageEnergy_eq_angularScore (m : ℕ) {s : ℝ} (hs : 0 < s)
    (x : Fin (2*m) → ℝ) :
    imageEnergy s x = 1 - (2*sqrt (π/s)*exp (-(π^2)/s)/((2*m : ℕ):ℝ)) *
      angularScore (exp (-(π^2)/s)) x := by
  let c := sqrt (π/s)
  let q := exp (-(π^2)/s)
  have hneutral : (∑ i : Fin (2*m), ∑ j : Fin (2*m), charge i * charge j) = 0 := by
    simp only [← Finset.mul_sum, charge_sum_even, mul_zero, Finset.sum_const_zero]
  have hp (i j : Fin (2*m)) :
      charge i * charge j * kernel s (x j-x i) =
        c*(charge i*charge j) +
        (2*c*q)*(charge i*charge j*angularK q (2*π*(x j-x i))) := by
    rw [kernel_eq_angularK hs]
    dsimp [c, q]
    ring
  have hsum :
      (∑ i, ∑ j, charge i * charge j * kernel s (x j-x i)) =
        c*(∑ i : Fin (2*m), ∑ j : Fin (2*m), charge i * charge j) +
        (2*c*q)*angularScore q x := by
    simp only [hp, angularScore, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hneutral, mul_zero, zero_add] at hsum
  rw [imageEnergy, hsum]
  dsimp [c, q]
  ring

/-- Equation (3), before the semicircle inequality. This equality quantifies
all coordinates and all positive widths. -/
theorem angular_deficit_eq (m : ℕ) (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (x : Fin (2*m) → ℝ) :
    let N : ℝ := ((2*m : ℕ) : ℝ)
    let c := sqrt (π/s)
    let q := exp (-(π^2)/s)
    let I := 1 - 2 * (kernel s 0 - kernel s (1/2)) / N
    N * (imageEnergy s x - I) / (2*c*q) =
      2*(angularK q 0 - angularK q π) - angularScore q x := by
  dsimp only
  rw [imageEnergy_eq_angularScore m hs, kernel_eq_angularK hs, kernel_eq_angularK hs]
  rw [mul_zero, show 2*π*(1/2:ℝ) = π by ring]
  have hn : (((2*m : ℕ):ℝ)) ≠ 0 := by positivity
  have hc : sqrt (π/s) ≠ 0 := (sqrt_pos.mpr (div_pos pi_pos hs)).ne'
  field_simp [hn, hc, (exp_pos (-(π^2)/s)).ne']
  ring

end GaussianChains
