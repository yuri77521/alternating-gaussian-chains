import StripSmallReduction
import StripBlockProfile
import ClustersRotation

/-! The full small-floor analytic reduction of Theorem 5. The distinguished
gap may be any largest gap. The final description only requires a cyclic
starting point and a translation of the six labelled sites. -/
noncomputable section
namespace GaussianChains.Strip
open Real PackedFace

private theorem aligned_profiles {s h : ℝ} (hs : 0<s) (hh : 0<h) (hh' : h<1/6)
    (hη : 2*π*h ≤ π/5) (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x)
    (hl : largestLast x) (hA : labelledSupport h x ∈ offEdgeReps)
    (hA0 : labelledSupport h x ≠ {0})
    (halign : structureFactor x 1 = (‖structureFactor x 1‖:ℂ)) :
    let A := labelledSupport h x
    ∀ k : Fin 6, k.val < blockCount A →
      ∃ B ψ : ℕ → ℝ, IsLocalMax (profile 0 (exp (-(π^2)/s)) B ψ) (blockMid x h A k) ∧
        (∀ t, profileTerm 0 1 (exp (-(π^2)/s)) B ψ t =
          ‖structureFactor x 1‖*cos (t-(peakIndex A k:ℝ)*(π/2))) ∧
        |B 2| ≤ 8 ∧ ∀ n ≥ 3, |B n| ≤ 10*(n:ℝ) := by
  intro A k hk
  have hlen := (block_bounds A k hk).1
  have hu := off_edge_lengths A hA hA0 k hk
  let b : Fin 4 := ⟨blockLength A k-1, by omega⟩
  have hb : blockLength A k=b.val+1 := by dsimp [b]; omega
  obtain ⟨B,ψ,hm,hf,h2,hharm⟩ := ground_block_profile hs hh hh' hη hx hl halign k hk b hb
  have hc : blockMid x h A k = blockCenter x (blockStart A k) b h := by
    simp [blockMid,blockCenter,startLift,lengthLift,ne_of_lt hk,hb]
  have hp : (peakIndex A k:ℝ)*(π/2) = blockPeak (blockStart A k) b := by
    rw [peak_index_formula A k hk,hb,blockPeak,blockQuadrant]
    have parity : ((b.val+1)%2=0) ↔ b.val%2=1 := by omega
    simp [parity]
  exact ⟨B,ψ,by simpa only [hc] using hm, fun t => by rw [hp]; exact hf t,h2,hharm⟩

private theorem small_exclude_aligned {s h : ℝ} (hh : 0<h) (hband : BroadSmall s h ∨ NarrowSmall s h)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) (hl : largestLast x)
    (halign : structureFactor x 1 = (‖structureFactor x 1‖:ℂ)) : labelledSupport h x ∉ offEdgeReps := by
  intro hA
  let A := labelledSupport h x
  have h10 : h ≤ 1/10 := hband.elim (fun hg => by linarith [hg.2.2]) (fun hn => hn.2.2)
  have hs : 0 < s := hband.elim (fun H => by linarith [H.1]) (fun H => by linarith [H.1])
  have hη : 2*π*h ≤ π/5 := by nlinarith only [mul_le_mul_of_nonneg_left h10 pi_pos.le]
  have hprof := aligned_profiles hs hh (by linarith) hη x hx hl hA
    (canonical_not_zero hh hband hx hl) halign
  rcases hband with hB|hN
  · obtain ⟨h8,h9,hr⟩ := hB
    have ha := broad_minimizer_amplitude h8 h9 hh.le hr hx.1 hx.2
    have hp := broad_peak_tests ha
    have ht := broad_tail_constants h8 h9
    have hn : InPeakArcs x h A (46/100) :=
      peak_arcs_from_profiles A x hs (by norm_num) (by linarith [pi_gt_three]) (by linarith)
        ⟨ht.2.1.trans hp.1,ht.2.2.1.trans hp.2⟩ hprof
    exact broad_from_peak_arcs hh ⟨h8,h9,hr⟩ x hx hl hA hn
  · obtain ⟨h799,h801,hr⟩ := hN
    have ha := narrow_minimizer_amplitude h799 h801 hh.le hr hx.1 hx.2
    have hp := narrow_peak_tests ha
    have ht := narrow_tail_constants h799 h801
    have hn : InPeakArcs x h A (42/100) :=
      peak_arcs_from_profiles A x hs (by norm_num) (by linarith [pi_gt_three]) (by linarith)
        ⟨ht.2.1.trans hp.1,ht.2.2.1.trans hp.2⟩ hprof
    exact narrow_from_peak_arcs hh ⟨h799,h801,hr⟩ x hx hl hA hn

theorem small_floor_reduction {s h : ℝ} (hh : 0<h) (hB : BroadSmall s h ∨ NarrowSmall s h)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) :
    ∃ k : Fin 6, ∃ t : ℝ, PackedFace.feasible h t ∧
      ∀ i, shiftLifts positiveSix x k i = shiftLifts positiveSix x k 0 + PackedFace.sites h t i := by
  have h10 : h ≤ 1/10 := hB.elim (fun H => by linarith [H.2.2]) (fun H => H.2.2)
  refine full_domain_from_support_exclusion (by linarith) (fun y hy hl => ?_) x hx
  let a := alignmentShift y
  let z := fun i => y i-a
  have hz : IsGroundState positiveSix h s z := (groundState_sub_const_iff _ _ _ _ _).mpr hy
  have hg : gap positiveSix z = gap positiveSix y := funext (gap_sub_const positiveSix y a)
  have hlz : largestLast z := by unfold largestLast; rw [hg]; exact hl
  have ha : structureFactor z 1=(‖structureFactor z 1‖:ℂ) := by
    calc structureFactor z 1 = (‖structureFactor y 1‖:ℂ) := structureFactor_align y
         _ = (‖structureFactor z 1‖:ℂ) := congrArg Complex.ofReal (norm_structureFactor_sub_const y a 1).symm
  have H := small_exclude_aligned hh hB z hz hlz ha
  unfold labelledSupport at H ⊢
  rwa [hg] at H

#print axioms small_floor_reduction
end GaussianChains.Strip
