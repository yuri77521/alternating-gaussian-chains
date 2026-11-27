import ClustersLock
import ClusterSeriesTwo

namespace GaussianChains

open Real ClusterSeries Filter Topology
open scoped Asymptotics

private theorem lock_gap_feasible {m : ℕ} (hm : 2 ≤ m) {h : ℝ} (hh : 0 ≤ h)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2)) :
    h ≤ 1/((2*m:ℕ):ℝ) := by
  have hN : 0 < 2*(m:ℝ) := by exact_mod_cast (by omega : 0 < 2*m)
  have hC : 1 ≤ 1+3*π*(m:ℝ)^2 := by linarith [mul_nonneg (by positivity : 0 ≤ 3*π) (sq_nonneg (m:ℝ))]
  have hCsq := one_le_pow₀ hC (n := 2)
  have hd := le_mul_of_one_le_right hN.le hCsq
  have hu := one_div_le_one_div_of_le hN hd
  push_cast
  exact le_trans (le_mul_of_one_le_left hh (by linarith [pi_gt_three])) (hsmall.trans hu)

/-- Corollary 2, Eq. (6), with any balanced ordered split of the given even
number of sites. The energy on the left minimizes over the entire feasible cell. -/
theorem corollary_two_exact {m : ℕ} (hm : 2 ≤ m) {s h : ℝ} (hs : 0<s) (hh : 0<h)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2))
    (k l : ℕ) (count : k+l=m-1) (hk : k≤l+1) (hl : l≤k+1) :
    minimumEnergy (by omega : 0 < 2*m) h s =
      1 - 2*sqrt (π/s)/((2*m:ℕ):ℝ) * packedMass k l (exp (-(π^2)/s)) (2*π*h) := by
  exact minimumEnergy_eq_of_locking (by omega) hs hh.le (lock_gap_feasible hm hh.le hsmall)
    (fun _ hx => groundState_isBalancedPacked hm hs hh hR hsmall hx) k l (by omega) hk hl

/-- Corollary 2, Eq. (7), at fixed width and particle count. The polynomial
contains the kernel dipole, odd second/fourth moments and even fourth moment.
The asymptotic variable is angular gap η; the actual floor is η/(2π). -/
theorem corollary_two_fourth {m : ℕ} (hm : 2 ≤ m) {s : ℝ} (hs : 0<s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (k l : ℕ)
    (count : k+l=m-1) (hk : k≤l+1) (hl : l≤k+1) :
    (fun η : ℝ => minimumEnergy (by omega : 0 < 2*m) (η/(2*π)) s -
      energyPoly k l (2*m) s η) =O[𝓝[>] 0] (fun η : ℝ => η^6) := by
  apply minimumEnergy_fourth_of_locking (by omega) hs k l (by omega) hk hl
  have hm' : (0:ℝ) < m := by exact_mod_cast (by omega : 0<m)
  have hb : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [hb,self_mem_nhdsWithin] with η hη hpos
  intro x hx
  have hfloor : 0 < η/(2*π) := div_pos hpos (by positivity)
  apply groundState_isBalancedPacked hm hs hfloor hR _ hx
  rw [show 2*π*(η/(2*π))=η by field_simp]
  exact hη.le

#print axioms corollary_two_exact
#print axioms corollary_two_fourth

/-- In the two-particle case the quadratic and quartic coefficients vanish:
Equation (7) is an equality with zero remainder on the whole feasible interval. -/
theorem corollary_two_pair_polynomial {s h : ℝ} (hs : 0<s)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (h₀ : 0≤h) (h₁ : h≤1/2) :
    minimumEnergy (by decide : 0 < 2) h s = energyPoly 0 0 2 s (2*π*h) := by
  rw [minimumEnergy_two_eq_dipole hs hR h₀ h₁]
  simp [energyPoly, coeff]

#print axioms corollary_two_pair_polynomial

end GaussianChains

