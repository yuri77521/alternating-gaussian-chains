import BandPhysical
import BandReplay
import StripChamberReduction
import CertTreeWidthOrder

/-! From support packets over a floor interval to a statement about all
ground states on the six-dimensional labelled simplex. Tied largest gaps
are covered by the non-strict chamber inequalities. -/
noncomputable section
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip

theorem full_domain_from_checked_packets {s h c t : ℝ} (hs : 0 < s) (hh : h < 1/6)
    (ht : 0 < t) {F : ℕ → ℝ → ℝ} (h0 : ∀ d, F 0 d = c + t * kernel s d)
    (h1 : ∀ d, F 1 d = t * deriv (kernel s) d)
    (h2 : ∀ d, F 2 d = t * deriv (deriv (kernel s)) d)
    (test : Support → Box 6 → Witness → Bool) (trialId : Support → Fin 5)
    (data : Support → String)
    (leaf : ∀ A ∈ offEdgeReps, ∀ B r u, test A B r = true → B.Mem u →
      simplex u → activeSupport u = A → (∀ i, u i ≤ u 5) →
      Stationary A (trialId A) F h u → False)
    (accepted : ∀ A ∈ offEdgeReps, checkPacket (test A) (initial A) (data A) = true)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) :
    ∃ k : Fin 6, ∃ v : ℝ, PackedFace.feasible h v ∧
      ∀ i, shiftLifts positiveSix x k i = shiftLifts positiveSix x k 0 + PackedFace.sites h v i := by
  apply full_domain_from_support_exclusion hh _ x hx
  intro y hy hm hin
  let u := slack h (gap positiveSix y)
  let A := activeSupport u
  have hA : A ∈ offEdgeReps := hin
  have hu : simplex u := slack_simplex hh ⟨hy.1, sum_gap _ _⟩
  have hmax (i : Fin 6) : u i ≤ u 5 :=
    div_le_div_of_nonneg_right (sub_le_sub_right (hm i) h) (by linarith)
  let P (w : Fin 6 → ℝ) := simplex w ∧ activeSupport w = A ∧ (∀ i, w i ≤ w 5) ∧
    Stationary A (trialId A) F h w
  have hn : ¬ P u := checkPacket_sound (P := P)
    (fun B r w hb hw hp => leaf A hA B r w hb hw hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
    (initial A) (data A) (accepted A hA) (initial_mem hu hmax) hu.2 hmax
  exact hn ⟨hu, rfl, hmax, groundState_stationary hs hh ht h0 h1 h2 y hy hm _⟩

/-- Appendix A uses the width-matched kernel at reference width a. Its
nonconstant derivatives have the same positive scale as the physical score. -/
theorem full_domain_from_matched_packets {a s h : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hh : h < 1/6) (test : Support → Box 6 → Witness → Bool) (trialId : Support → Fin 5)
    (data : Support → String)
    (leaf : ∀ A ∈ offEdgeReps, ∀ B r u, test A B r = true → B.Mem u →
      simplex u → activeSupport u = A → (∀ i, u i ≤ u 5) →
      Stationary A (trialId A) (fun p => deriv^[p] (WidthBounds.matched a s)) h u → False)
    (accepted : ∀ A ∈ offEdgeReps, checkPacket (test A) (initial A) (data A) = true)
    (x : Fin 6 → ℝ) (hx : IsGroundState positiveSix h s x) :
    ∃ k : Fin 6, ∃ v : ℝ, PackedFace.feasible h v ∧
      ∀ i, shiftLifts positiveSix x k i = shiftLifts positiveSix x k 0 + PackedFace.sites h v i := by
  apply full_domain_from_checked_packets hs hh (WidthBounds.coefficient_pos ha hs)
    (c := WidthBounds.offset a s) (F := fun p => deriv^[p] (WidthBounds.matched a s))
    _ _ _ test trialId data leaf accepted x hx
  · intro d
    exact (WidthBounds.matched_affine a s d).trans (add_comm _ _)
  · exact WidthBounds.matched_deriv_mul hs 0
  · exact WidthBounds.matched_deriv_mul hs 1

end GaussianChains.Band
