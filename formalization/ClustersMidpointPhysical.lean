import ClustersMidpointKernel
import ClustersSelectionPhysical
import ClusterSeriesCandidate

/-! Inside the two-packed-block stratum, compare the actual ground-state
image energy with the feasible antipodal centered competitor. -/
noncomputable section
open Real
namespace GaussianChains.Clusters

/-- The first packed midpoint is displaced from zero by `v` radians;
the other is at π. Positions returned by this definition are in periods. -/
def packedJoined (k l : ℕ) (η v : ℝ) : Fin ((2*k+1)+(2*l+1)) → ℝ :=
  joinedBlocks (fun i => v+packedOffset η i) (packedOffset η)

theorem packedJoined_center (k l : ℕ) (h : ℝ) :
    packedJoined k l (2*π*h) 0 = ClusterSeries.packedSites k l h := by
  funext n
  refine Fin.addCases (fun i => ?_) (fun j => ?_) n
  · simp [packedJoined, joinedBlocks, ClusterSeries.packedSites, ClusterSeries.packedAngle,
      packedOffset, i.isLt]
  · simp [packedJoined, joinedBlocks, ClusterSeries.packedSites, ClusterSeries.packedAngle,
      packedOffset]
    omega

private theorem within_translate {I : Type*} [Fintype I]
    (w x : I → ℝ) (K : ℝ → ℝ) (v : ℝ) :
    blockSum w w (fun i => v+x i) (fun i => v+x i) K 0 = blockSum w w x x K 0 := by
  simp only [blockSum, add_sub_add_left_eq_sub]

/-- The subtracted scores have identical two within-block contributions;
only the ordered cross interaction survives. -/
theorem packedJoined_score_difference (k l : ℕ) (q η v : ℝ) :
    angularScore q (packedJoined k l η 0) - angularScore q (packedJoined k l η v) =
      packedCross k l η (angularK q) v - packedCross k l η (angularK q) 0 := by
  unfold packedJoined
  rw [joined_angularScore, joined_angularScore]
  simp_rw [within_translate]
  rw [packed_cross_eq_blockSum, packed_cross_eq_blockSum]
  change _ = 2 * blockSum charge charge _ _ _ _ - 2 * blockSum charge charge _ _ _ _
  ring

/-- For any localized pair of packed odd progressions that actually minimizes
the full image energy, the midpoint separation is π. This conditional step
of the classification does not assume the counts are balanced. -/
theorem groundState_packed_midpoint (k l : ℕ) {h s C v : ℝ}
    (hs : 0 < s) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (hC : 2 ≤ C) (hh : 0 ≤ h)
    (hsmall : 2*π*h ≤ 1/((((2*k+1 : ℕ) : ℝ)+((2*l+1 : ℕ) : ℝ))*C^2))
    (hloc : ∀ (i : Fin (2*k+1)) (j : Fin (2*l+1)),
      |v + (packedOffset (2*π*h) i - packedOffset (2*π*h) j)| ≤ 2*C*(2*π*h))
    (hground : IsGroundState (by omega) h s (packedJoined k l (2*π*h) v)) :
    v = 0 := by
  let q := exp (-(π^2)/s)
  have hq : q < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos pi_pos)) hs)
  apply packed_midpoint_locked k l (q := q) (exp_pos _).le hq hR hC (by positivity) hsmall hloc
  have he := hground.2 _ (ClusterSeries.packedSites_feasible k l h (floor_le_mean hground.1))
  rw [← packedJoined_center k l h] at he
  have hsco {N : ℕ} (hN : ∃ m, N = 2*m) (x : Fin N → ℝ) :
      imageEnergy s x = 1-(2*sqrt (π/s)*q/(N:ℝ))*angularScore q x := by
    obtain ⟨m,rfl⟩ := hN
    exact imageEnergy_eq_angularScore m hs x
  have hev : ∃ m, (2*k+1)+(2*l+1) = 2*m := ⟨k+l+1, by omega⟩
  rw [hsco hev, hsco hev] at he
  have hfac : 0 < 2*sqrt (π/s)*q/(((2*k+1)+(2*l+1) : ℕ) : ℝ) := by
    dsimp [q]
    positivity
  rw [sub_le_sub_iff_left, mul_le_mul_iff_right₀ hfac] at he
  linarith only [packedJoined_score_difference k l q (2*π*h) v, he]

#print axioms groundState_packed_midpoint

/-- Both charts may have arbitrary midpoint offsets. Rigid translation
places the second one at π and preserves every gap and the energy. -/
theorem groundState_packed_offsets_equal (k l : ℕ) {h s C a b : ℝ}
    (hs : 0 < s) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (hC : 2 ≤ C) (hh : 0 ≤ h)
    (hsmall : 2*π*h ≤ 1/((((2*k+1 : ℕ) : ℝ)+((2*l+1 : ℕ) : ℝ))*C^2))
    (hx : ∀ i : Fin (2*k+1), |a+packedOffset (2*π*h) i| ≤ C*(2*π*h))
    (hy : ∀ j : Fin (2*l+1), |b+packedOffset (2*π*h) j| ≤ C*(2*π*h))
    (hg : IsGroundState (by omega) h s (joinedBlocks (fun i : Fin (2*k+1) => a+packedOffset (2*π*h) i)
      (fun j : Fin (2*l+1) => b+packedOffset (2*π*h) j))) : a = b := by
  let X := joinedBlocks (fun i : Fin (2*k+1) => a+packedOffset (2*π*h) i)
    (fun j : Fin (2*l+1) => b+packedOffset (2*π*h) j)
  have move : packedJoined k l (2*π*h) (a-b) = fun i => X i - b/(2*π) := by
    funext n
    refine Fin.addCases (fun i => ?_) (fun j => ?_) n <;>
      simp only [packedJoined, joinedBlocks, X, Fin.append_left, Fin.append_right] <;> ring
  have hg' : IsGroundState (by omega) h s (packedJoined k l (2*π*h) (a-b)) := by
    rw [move]
    refine ⟨fun i => ?_, fun y hY => ?_⟩
    · have hgap : gap (by omega) (fun j => X j - b/(2*π)) i = gap (by omega) X i := by
        simp only [gap, liftSite]
        ring
      rw [hgap]
      exact hg.1 i
    · rw [imageEnergy_sub_const]
      exact hg.2 y hY
  apply sub_eq_zero.mp
  exact groundState_packed_midpoint k l hs hR hC hh hsmall
    (fun i j => by simpa only [mul_assoc] using packed_offsets_localized hx hy i j) hg'

#print axioms groundState_packed_offsets_equal
end GaussianChains.Clusters

