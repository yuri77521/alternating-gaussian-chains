import BandPhysicalReduction
import BandSchedule

/-! The trial, root chamber, and support used by the proof must be those
selected by the actual indexed packet for each of the eighteen supports. -/
noncomputable section
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip

theorem packetCheck_witness {slab : Slab} {b : Fin slab.count} {i : Fin 18}
    {test : Fin 5 → Box 6 → Witness → Bool} (hc : packetCheck slab b i test = true) :
    ∃ j : Fin 5, ∃ data : String, checkPacket (test j) (initial (support i)) data = true := by
  unfold packetCheck at hc
  split at hc
  · contradiction
  · split at hc
    · exact ⟨_, _, hc⟩
    · contradiction

theorem full_domain_from_scheduled_packets {s h : ℝ} (slab : Slab) (b : Fin slab.count)
    (hs : 0 < s) (hh : h < 1/6)
    (test : Support → Fin 5 → Box 6 → Witness → Bool)
    (leaf : ∀ A ∈ offEdgeReps, ∀ j B r u, test A j B r = true → B.Mem u →
      simplex u → activeSupport u = A → (∀ i, u i ≤ u 5) →
      Stationary A j (fun p => deriv^[p] (WidthBounds.matched slab.anchor s)) h u → False)
    (accepted : ∀ i : Fin 18, packetCheck slab b i (test (support i)) = true)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) :
    ∃ k : Fin 6, ∃ v : ℝ, PackedFace.feasible h v ∧
      ∀ i, shiftLifts positiveSix x k i = shiftLifts positiveSix x k 0 + PackedFace.sites h v i := by
  classical
  have H (A : Support) (hA : A ∈ offEdgeReps) :
      ∃ j : Fin 5, ∃ data : String, checkPacket (test A j) (initial A) data = true := by
    obtain ⟨i, rfl⟩ := support_covers hA
    exact packetCheck_witness (accepted i)
  let ids (A : Support) := if hA : A ∈ offEdgeReps then (H A hA).choose else 0
  let packets (A : Support) :=
    if hA : A ∈ offEdgeReps then (H A hA).choose_spec.choose else ""
  apply full_domain_from_matched_packets (a := (slab.anchor:ℝ)) (by cases slab <;> norm_num [Slab.anchor])
    hs hh (fun A => test A (ids A)) ids packets _ _ x hx
  · intro A hA
    exact leaf A hA (ids A)
  · intro A hA
    simpa [ids, packets, hA] using (H A hA).choose_spec.choose_spec

#print axioms full_domain_from_scheduled_packets

end GaussianChains.Band
