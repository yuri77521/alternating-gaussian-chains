import ChainSymmetry
import ClustersRotation
import ClustersSelectionPhysical
import ClustersMoments
import ClusterSeriesTrialMinimum

/-! Balanced counts for every ground state once the localization step has
split its ordered sites into arbitrary angular offsets at two antipodes. -/
noncomputable section
open Finset Real AlternatingMoments
namespace GaussianChains.Clusters

private theorem block_variance_floor (k : ℕ) (u : ℕ → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hu : ∀ i<2*k, η ≤ u (i+1)-u i) :
    (k:ℝ)*((k:ℝ)+1)*η^2 ≤ (∑ i : Fin (2*k+1), charge i*(u i.val)^2)-
      (∑ i : Fin (2*k+1), charge i*u i.val)^2 := by
  unfold charge
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i*(u i)^2),
    Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i*u i)]
  exact OddBlock.variance_lower u k hη hu

/-- The trial between the two most nearly equal odd sizes has cost
`⌊(k+l+1)²/2⌋`, independently of the split used for the given sites. -/
theorem balanced_trial_bound (k l : ℕ) {s h : ℝ} (hs : 0<s)
    (h0 : 0≤h) (h1 : h ≤ 1/(((2*k+1)+(2*l+1):ℕ):ℝ)) :
    let N := (2*k+1)+(2*l+1)
    let q := exp (-(π^2)/s)
    let c := sqrt (π/s)
    let η := 2*π*h
    (N:ℝ)*(minimumEnergy (by dsimp [N]; omega : 0<N) h s - ClusterSeries.dipoleEnergy N s)/(2*c*q) ≤
      (angularCos 2 q 0-angularCos 2 q π)*((((k+l+1)^2/2:ℕ):ℝ)*η^2) := by
  let a := (k+l)/2
  let b := k+l-a
  have hab : a+b=k+l := by dsimp [a,b]; omega
  have hA : a≤b+1 := by dsimp [a,b]; omega
  have hB : b≤a+1 := by dsimp [a,b]; omega
  have hN : (2*a+1)+(2*b+1) = (2*k+1)+(2*l+1) := by omega
  have hm := ClusterSeries.minimum_normalized_deficit_le a b hs h0 (by rwa [hN])
  dsimp only at hm ⊢
  simp only [hN] at hm
  have hc : ClusterSeries.coeff a + ClusterSeries.coeff b =
      ((((k+l+1)^2/2:ℕ):ℝ)) := by
    rw [← hab, ← balanced_split_cost hA hB]
    simp [splitCost,ClusterSeries.coeff]
  rw [hc] at hm
  linarith only [hm]

/-- For any localized pair of odd clusters, **global minimality for the
actual image energy** implies balanced cardinalities. All internal gap
floors are recovered from feasibility and the cyclic inequalities. -/
theorem joined_groundState_balanced (k l : ℕ) (u v : ℕ → ℝ)
    {s C h : ℝ} (hs : 0<s) (hC : 0<C) (hh : 0<h)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/((((2*k+1)+(2*l+1):ℕ):ℝ)*C^2))
    (hu : ∀ i<2*k+1, |u i| ≤ C*(2*π*h))
    (hv : ∀ i<2*l+1, |v i| ≤ C*(2*π*h))
    (hg : IsGroundState (by omega) h s (joinedSites k l u v)) :
    k ≤ l+1 ∧ l ≤ k+1 := by
  let N := (2*k+1)+(2*l+1)
  let q := exp (-(π^2)/s)
  let c := sqrt (π/s)
  let η := 2*π*h
  let D := angularCos 2 q 0-angularCos 2 q π
  let F := (N:ℝ)*(imageEnergy s (joinedSites k l u v)-ClusterSeries.dipoleEnergy N s)/(2*c*q)
  let P₀ := ∑ i : Fin (2*k+1), charge i*u i.val
  let Pπ := ∑ i : Fin (2*l+1), charge i*v i.val
  let V₀ := (∑ i : Fin (2*k+1), charge i*(u i.val)^2)-P₀^2
  let Vπ := (∑ i : Fin (2*l+1), charge i*(v i.val)^2)-Pπ^2
  let Kπ := -angularCos 2 q π
  let R := F-(D*(V₀+Vπ)+Kπ*(P₀-Pπ)^2)
  have hq : 0<q := exp_pos _
  have hq' : q<1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos pi_pos)) hs)
  have hη : 0<η := by dsimp [η]; positivity
  have hN : 0<(N:ℝ) := by dsimp [N]; positivity
  have hgaps := (joinedBlocks_feasible_iff k l u v h).mp hg.1
  have hV₀ : (k:ℝ)*((k:ℝ)+1)*η^2 ≤ V₀ := block_variance_floor k u hη.le hgaps.1
  have hVπ : (l:ℝ)*((l:ℝ)+1)*η^2 ≤ Vπ := block_variance_floor l v hη.le hgaps.2.1
  have hvar : (splitCost k l : ℝ)*η^2 ≤ V₀+Vπ := by
    simp only [splitCost,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    linarith only [hV₀,hVπ]
  have ht := imageEnergy_joined_taylor k l (fun i => u i.val) (fun i => v i.val)
    hs hR (fun i => hu i.val i.isLt) (fun i => hv i.val i.isLt)
  have hrem : |R| ≤ 4/3*(N:ℝ)^2*C^4*η^4 := by
    dsimp only [R, F, D, V₀, Vπ, P₀, Pπ, Kπ, c, q, η, N, joinedSites, ClusterSeries.dipoleEnergy]
    simpa only [sub_eq_add_neg,neg_mul] using ht
  have htrial : F ≤ D*((((k+l+1)^2/2:ℕ):ℝ)*η^2) := by
    dsimp only [F]
    rw [groundState_energy_eq_minimum hg]
    exact balanced_trial_bound k l hs hh.le (floor_le_mean hg.1)
  exact split_of_taylor_bound (D := D) (Kπ := Kπ) (Δ := P₀-Pπ) (R := R) (F := F)
    hN hC hη hsmall (locking_D_bounds hq.le hq' hR).1
    ((by norm_num : (0:ℝ)≤5/6).trans (locking_curvature_bounds hq.le hq' hR π).2.2)
    hvar hrem (by dsimp only [R]; ring) htrial

#print axioms joined_groundState_balanced

/-- Angular offsets of an arbitrary cyclically cut physical lift. -/
def recutOffsets {N : ℕ} (hN : 0<N) (x : Fin N → ℝ) (start : ℕ) (phase : ℝ) (n : ℕ) :=
  2*π*liftSite hN x (start+n) - phase

/-- Given any division into consecutive odd blocks, the joined chart exactly
recovers the cyclically relabeled cell, up to the chosen translation. -/
theorem joinedSites_recut (k l : ℕ) (x : Fin ((2*k+1)+(2*l+1)) → ℝ)
    (t : Fin ((2*k+1)+(2*l+1))) (phase : ℝ) :
    joinedSites k l (recutOffsets (by omega) x t.val phase)
      (recutOffsets (by omega) x (t.val+(2*k+1)) (phase+π)) =
      fun i => shiftLifts (by omega) x t i - phase/(2*π) := by
  funext i
  rw [joined_eval]
  unfold recutOffsets shiftLifts
  split_ifs with hi
  · rw [Nat.add_comm t.val i.val]
    field_simp [pi_ne_zero] <;> ring
  · rw [show t.val+(2*k+1)+(i.val-(2*k+1)) = i.val+t.val by omega]
    field_simp [pi_ne_zero]
    <;> ring

/-- This chart preserves the full constrained minimum even when its first
label is odd (both signs in every pair are then reversed). -/
theorem groundState_recut (k l : ℕ) (x : Fin ((2*k+1)+(2*l+1)) → ℝ)
    (t : Fin ((2*k+1)+(2*l+1))) (phase h s : ℝ) :
    IsGroundState (by omega) h s
      (joinedSites k l (recutOffsets (by omega) x t.val phase)
        (recutOffsets (by omega) x (t.val+(2*k+1)) (phase+π))) ↔
      IsGroundState (by omega) h s x := by
  rw [joinedSites_recut]
  let N := (2*k+1)+(2*l+1)
  have hN : 0<N := by dsimp [N]; omega
  letI : NeZero N := ⟨hN.ne'⟩
  have he : 2 ∣ N := ⟨k+l+1, by dsimp [N]; omega⟩
  let X := shiftLifts hN x t
  have hg : Feasible hN h (fun i => X i - phase/(2*π)) ↔ Feasible hN h x := by
    change (∀ i, h ≤ gap hN (fun j => X j - phase/(2*π)) i) ↔ _
    simp only [gap_sub_const]
    exact feasible_shiftLifts_iff hN h x t
  have hE : imageEnergy s (fun i => X i-phase/(2*π)) = imageEnergy s x :=
    (imageEnergy_sub_const _ _ _).trans (imageEnergy_shiftLifts hN he s x t)
  change (Feasible hN h (fun i => X i - phase/(2*π)) ∧
    ∀ y, Feasible hN h y → imageEnergy s (fun i => X i - phase/(2*π)) ≤ imageEnergy s y) ↔ _
  rw [hg,hE] <;> rfl


/-- Applied directly to the original physical coordinates after a cyclic
cut, the sole geometric input is that both odd blocks lie in the specified
angular neighborhoods. -/
theorem localized_groundState_balanced (k l : ℕ) (x : Fin ((2*k+1)+(2*l+1)) → ℝ)
    (t : Fin ((2*k+1)+(2*l+1))) (phase : ℝ) {s C h : ℝ}
    (hs : 0<s) (hC : 0<C) (hh : 0<h)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/((((2*k+1)+(2*l+1):ℕ):ℝ)*C^2))
    (hu : ∀ i<2*k+1, |recutOffsets (by omega) x t.val phase i| ≤ C*(2*π*h))
    (hv : ∀ i<2*l+1, |recutOffsets (by omega) x (t.val+(2*k+1)) (phase+π) i| ≤ C*(2*π*h))
    (hg : IsGroundState (by omega) h s x) : k ≤ l+1 ∧ l ≤ k+1 :=
  joined_groundState_balanced k l _ _ hs hC hh hR hsmall hu hv
    ((groundState_recut k l x t phase h s).mpr hg)

#print axioms localized_groundState_balanced

end GaussianChains.Clusters

