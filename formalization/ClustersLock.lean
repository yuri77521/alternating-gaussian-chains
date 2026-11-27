import ClustersLocalizedCut
import ClustersLockedChart
import ClusterSeriesLocking
import ClusterSeriesOrbitsSwap

noncomputable section
namespace GaussianChains

open Real Clusters ClusterSeries

/-- Necessity in Theorem 1 for `N = 2m ≥ 4`. The hypothesis uses the
published fourth frequency moment, and the small spacing is the angular
spacing `2πh`. A recut of either parity is retained in `IsBalancedPacked`. -/
theorem groundState_isBalancedPacked {m : ℕ} (hm : 2 ≤ m) {hN : 0 < 2*m}
    {s h : ℝ} (hs : 0<s) (hh : 0<h) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2))
    {x : Fin (2*m) → ℝ} (hx : IsGroundState hN h s x) :
    IsBalancedPacked hN h x := by
  let C := 1+3*π*(m:ℝ)^2
  have hC : 2 ≤ C := by
    have hm' : 2 ≤ (m:ℝ) := by exact_mod_cast hm
    dsimp [C]
    nlinarith [pi_gt_three, mul_nonneg (sub_nonneg.mpr pi_gt_three.le)
      (sq_nonneg (m:ℝ)), sq_nonneg ((m:ℝ)-1)]
  obtain ⟨p,k,l,a,hp,e,hu,hv⟩ := groundState_localized_cut hm hs hh hR hsmall hx
  let t : Fin (2*m) := ⟨p,hp⟩
  obtain ⟨hk,hl,c,hcoord⟩ := groundState_locks_in_chart hN k l e.symm x t a hs hh hC
    hR (by simpa only [Nat.cast_mul,Nat.cast_ofNat,C] using hsmall)
    (fun i hi => hu ⟨i,hi⟩) (fun j hj => hv ⟨j,hj⟩) hx
  exact ⟨k,l,e.symm,hk,hl,t,c,hcoord⟩

private theorem locking_floor_lt_mean {m : ℕ} (hm : 2 ≤ m) {h : ℝ} (hh : 0 < h)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2)) : h < 1/((2*m:ℕ):ℝ) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hC : 1 ≤ 1+3*π*(m:ℝ)^2 := by linarith [mul_nonneg (by positivity : 0≤3*π) (sq_nonneg (m:ℝ))]
  have hC₂ : 1 ≤ (1+3*π*(m:ℝ)^2)^2 := one_le_pow₀ hC
  have hs' := (le_div_iff₀ (by positivity : 0 < 2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2)).mp hsmall
  rw [Nat.cast_mul,Nat.cast_ofNat,lt_div_iff₀ (by positivity)]
  calc
    _ < (2*π*h)*(2*(m:ℝ)) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.mpr pi_gt_three.le) hh.le]
    _ ≤ (2*π*h)*(2*(m:ℝ))*(1+3*π*(m:ℝ)^2)^2 :=
      le_mul_of_one_le_right (by positivity) hC₂
    _ ≤ 1 := by linarith only [hs']

/-- Theorem 1 for all even counts at least four. Both directions classify
the same ground states as the general ordered energy; no feasibility
assumption on the test configuration is needed. The two-site statement is
`two_site_classification`, which holds for every feasible floor. -/
theorem exact_cluster_locking {m : ℕ} (hm : 2 ≤ m) {hN : 0 < 2*m}
    {s h : ℝ} (hs : 0<s) (hh : 0<h) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2))
    (x : Fin (2*m) → ℝ) : IsGroundState hN h s x ↔ IsBalancedPacked hN h x :=
  groundState_iff_of_locking hN hs hh.le (locking_floor_lt_mean hm hh hsmall).le
    (fun _ hx => groundState_isBalancedPacked hm hs hh hR hsmall hx) x

/-- Any two ground states, including the two orders of an unequal split,
are canonically described by integer recuts. Recuts with different parity
are species-equivalent exactly when the two odd block lengths agree. -/
theorem cluster_ground_state_orbits {m : ℕ} (hm : 2 ≤ m) {hN : 0 < 2*m}
    {s h : ℝ} (hs : 0<s) (hh : 0<h) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2))
    (k l : ℕ) (he : 2*m=(2*k+1)+(2*l+1)) (hkl : k≤l+1) (hlk : l≤k+1)
    {x y : Fin (2*m) → ℝ} (hx : IsGroundState hN h s x) (hy : IsGroundState hN h s y) :
    let P := integerSite (by omega) (packedSites k l h)
    ∃ t u : ℤ, ∃ c d : ℝ, (∀ i, integerSite hN x i = P (i+t)+c) ∧
      (∀ i, integerSite hN y i = P (i+u)+d) ∧
      (SameSpeciesSites (integerSite hN x) (integerSite hN y) ↔ t%2=u%2 ∨ k=l) :=
  balancedPacked_pair_orbits k l he hkl hlk (he ▸ locking_floor_lt_mean hm hh hsmall) x y
    (groundState_isBalancedPacked hm hs hh hR hsmall hx)
    (groundState_isBalancedPacked hm hs hh hR hsmall hy)

#print axioms exact_cluster_locking
#print axioms cluster_ground_state_orbits

/-- Both candidate arrangements actually minimize. Every minimizer lies in
one of their species-preserving isometry orbits, which coincide exactly for
equal block lengths. The odd recut exchanging them is `packedSites_swap_lift`. -/
theorem cluster_ground_state_representatives {m : ℕ} (hm : 2 ≤ m) {hN : 0 < 2*m}
    {s h : ℝ} (hs : 0<s) (hh : 0<h) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2))
    (k l : ℕ) (he : 2*m=(2*k+1)+(2*l+1)) (hkl : k≤l+1) (hlk : l≤k+1) :
    let he' : 2*m=(2*l+1)+(2*k+1) := he.trans (Nat.add_comm _ _)
    let P := integerSite (by omega) (packedSites k l h)
    let Q := integerSite (by omega) (packedSites l k h)
    IsGroundState hN h s (fun i => packedSites k l h (Fin.cast he i)) ∧
    IsGroundState hN h s (fun i => packedSites l k h (Fin.cast he' i)) ∧
    (SameSpeciesSites P Q ↔ k=l) ∧ ∀ x : Fin (2*m) → ℝ, IsGroundState hN h s x →
      SameSpeciesSites (integerSite hN x) P ∨ SameSpeciesSites (integerSite hN x) Q := by
  have H := exact_cluster_locking (hN := hN) hm hs hh hR hsmall
  obtain ⟨hEq,hcover⟩ := balancedPacked_representatives (hm := hN) k l he hkl hlk
    (he ▸ locking_floor_lt_mean hm hh hsmall)
  exact ⟨(H _).mpr (balancedPacked_of_canonical hN h k l he hkl hlk),
    (H _).mpr (balancedPacked_of_canonical hN h l k (he.trans (Nat.add_comm _ _)) hlk hkl),
    hEq, fun x hx => hcover x ((H x).mp hx)⟩

#print axioms cluster_ground_state_representatives

end GaussianChains
