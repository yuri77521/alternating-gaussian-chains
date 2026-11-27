import ClustersRotation
import ClustersMidpointPhysical

/-! Converting equality of all active angular gaps into the actual canonical
cell. Translating both blocks by the second midpoint matches the normalized
coordinate convention used by the midpoint curvature theorem. -/
noncomputable section
namespace GaussianChains.Clusters
open Real

/-- A tight odd block is its midpoint plus the centered arithmetic progression. -/
theorem tight_block_coords (k : ℕ) (u : ℕ → ℝ) {η : ℝ}
    (hg : ∀ i < 2*k, u (i+1) - u i = η) (i : Fin (2*k+1)) :
    u i.val = u k + packedOffset η i := by
  have h (n : ℕ) (hn : n ≤ 2*k) : u n = u 0 + (n:ℝ)*η := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := hg n (by omega)
      rw [Nat.cast_succ]
      nlinarith only [hstep, ih (by omega)]
  unfold packedOffset
  have hi := i.isLt
  nlinarith only [h i.val (by omega), h k (by omega)]

theorem joined_tight_translate (k l : ℕ) (u v : ℕ → ℝ) {η : ℝ}
    (hu : ∀ i < 2*k, u (i+1)-u i = η) (hv : ∀ j < 2*l, v (j+1)-v j = η) :
    (fun i => joinedSites k l u v i - v l / (2*π)) = packedJoined k l η (u k-v l) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [joinedSites, packedJoined, joinedBlocks, Fin.append_left]
    rw [tight_block_coords k u hu a]
    ring
  · simp only [joinedSites, packedJoined, joinedBlocks, Fin.append_right]
    rw [tight_block_coords l v hv b]
    ring

/-- For a localized pair of odd blocks with all internal gaps tight, actual
global minimality forces the two angular midpoint offsets to agree. Every site
is then the corresponding labelled canonical site plus the same translation. -/
theorem groundState_tight_blocks_are_antipodal (k l : ℕ) (u v : ℕ → ℝ) {h s C : ℝ}
    (hs : 0 < s) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (hC : 2 ≤ C) (hh : 0 ≤ h)
    (hsmall : 2*π*h ≤ 1/((((2*k+1 : ℕ) : ℝ)+((2*l+1 : ℕ) : ℝ))*C^2))
    (hu : ∀ i < 2*k, u (i+1)-u i = 2*π*h)
    (hv : ∀ j < 2*l, v (j+1)-v j = 2*π*h)
    (hul : ∀ i : Fin (2*k+1), |u i.val| ≤ C*(2*π*h))
    (hvl : ∀ j : Fin (2*l+1), |v j.val| ≤ C*(2*π*h))
    (hx : IsGroundState (by omega) h s (joinedSites k l u v)) :
    u k = v l ∧ ∀ i, joinedSites k l u v i = ClusterSeries.packedSites k l h i + v l/(2*π) := by
  have htrans := joined_tight_translate k l u v hu hv
  have hground := (groundState_sub_const_iff _ h s _ (v l/(2*π))).2 hx
  rw [htrans] at hground
  have hzero := groundState_packed_midpoint k l hs hR hC hh hsmall (fun i j => by
    have hu' (i : Fin (2*k+1)) : |u k + packedOffset (2*π*h) i| ≤ C*(2*π*h) := by
      rw [← tight_block_coords k u hu i]; exact hul i
    have hv' (j : Fin (2*l+1)) : |v l + packedOffset (2*π*h) j| ≤ C*(2*π*h) := by
      rw [← tight_block_coords l v hv j]; exact hvl j
    simpa only [mul_assoc] using packed_offsets_localized hu' hv' i j) hground
  rw [hzero, packedJoined_center] at htrans
  exact ⟨sub_eq_zero.mp hzero, fun i => sub_eq_iff_eq_add.mp (congrFun htrans i)⟩

#print axioms groundState_tight_blocks_are_antipodal

end GaussianChains.Clusters
