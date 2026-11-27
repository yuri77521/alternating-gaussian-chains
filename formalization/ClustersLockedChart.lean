import ClustersContact
import ClustersContactPacked
import ClustersSelectionBalanced

noncomputable section
namespace GaussianChains.Clusters

open Real ClusterSeries

/-- After the two odd localization charts have been identified, the
quantitative floor forces balance, all contacts, and antipodal midpoints.
The conclusion gives the original labelled cell, up to a cyclic cut and
a common translation, with every coordinate explicit. -/
theorem groundState_locks_in_chart {N : ℕ} (hN : 0 < N) (k l : ℕ)
    (e : N = (2*k+1)+(2*l+1)) (x : Fin N → ℝ) (t : Fin N) (a : ℝ)
    {h s C : ℝ} (hs : 0<s) (hh : 0<h) (hC : 2 ≤ C)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3) (hsmall : 2*π*h ≤ 1/((N:ℝ)*C^2))
    (hu : ∀ i<2*k+1, |2*π*liftSite hN x (t.val+i)-a| ≤ C*(2*π*h))
    (hv : ∀ j<2*l+1, |2*π*liftSite hN x (t.val+(2*k+1)+j)-(a+π)| ≤ C*(2*π*h))
    (hx : IsGroundState hN h s x) :
    k ≤ l+1 ∧ l ≤ k+1 ∧ ∃ c : ℝ,
      ∀ i : Fin N, shiftLifts hN x t i = packedSites k l h (Fin.cast e i)+c := by
  subst N
  let u := recutOffsets hN x t.val a
  let v := recutOffsets hN x (t.val+(2*k+1)) (a+π)
  have hg : IsGroundState hN h s (joinedSites k l u v) :=
    (groundState_recut k l x t a h s).mpr hx
  have hc' : 1 ≤ C := by linarith
  have hsmall' : 2*π*h ≤ 1 / ((((2*k+1:ℕ):ℝ)+((2*l+1:ℕ):ℝ))*C^2) := by
    simpa only [Nat.cast_add] using hsmall
  obtain ⟨hk,hl⟩ := joined_groundState_balanced k l u v hs (by linarith) hh hR hsmall hu hv hg
  obtain ⟨h₁,h₂⟩ := localized_groundState_contacts u v hs hh hc' hR hsmall' hu hv hg
  obtain ⟨_, hcoord⟩ := groundState_tight_blocks_are_antipodal k l u v hs hR hC hh.le hsmall'
    h₁ h₂ (fun i => hu _ i.isLt) (fun j => hv _ j.isLt) hg
  refine ⟨hk,hl,v l/(2*π)+a/(2*π),?_⟩
  intro i
  have hrec := congrFun (joinedSites_recut k l x t a) i
  change joinedSites k l u v i = shiftLifts hN x t i - a/(2*π) at hrec
  change shiftLifts hN x t i = packedSites k l h i + _
  linarith [hcoord i]

end GaussianChains.Clusters
