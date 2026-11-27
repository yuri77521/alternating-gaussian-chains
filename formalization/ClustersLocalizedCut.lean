import ClustersLocalizationPhysical
import ClustersJumpChart

/-! Selecting both odd blocks of a ground state in its original labelled coordinates. -/

noncomputable section
namespace GaussianChains.Clusters
open Real Localization JumpLocalization

/-- Under the exact floor and width hypotheses of Theorem 1 a cyclic cut
locates two consecutive, nonempty odd blocks at antipodal angular centers.
The second block may extend into the following copy of the physical cell. -/
theorem groundState_localized_cut {m : ℕ} (hm : 2 ≤ m) {hN : 0 < 2*m} {s h : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1/(2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2))
    {x : Fin (2*m) → ℝ} (hx : IsGroundState hN h s x) :
    ∃ p k l : ℕ, ∃ a : ℝ, p < 2*m ∧ (2*k+1)+(2*l+1)=2*m ∧
      (∀ i : Fin (2*k+1), |2*π*liftSite hN x (p+i.val)-a| ≤
        (1+3*π*(m:ℝ)^2)*(2*π*h)) ∧
      (∀ j : Fin (2*l+1), |2*π*liftSite hN x (p+(2*k+1)+j.val)-(a+π)| ≤
        (1+3*π*(m:ℝ)^2)*(2*π*h)) := by
  obtain ⟨d,hz,_,halign,_⟩ := exists_first_mode_aligned hN x h s hx.1
  let z (i : Fin (2*m)) := x i - d
  have hcost : 2 - (structureFactor z 1).re ≤ 3*(m:ℝ)^2*(2*π*h)^2 := by
    rw [show structureFactor z 1 = (‖structureFactor x 1‖:ℂ) from halign, Complex.ofReal_re]
    exact groundState_first_mode_cost_le hs hh.le hR hx
  obtain ⟨p,b,k,l,K,hpb,hb,hk,hl,_,hfirst,hlast⟩ :=
    two_odd_localized_blocks hz hh hcost hsmall
  have hshift (n : ℕ) : siteAngle hN z n = 2*π*liftSite hN x n - 2*π*d := by
    unfold siteAngle liftSite
    dsimp only [z]
    ring
  refine ⟨p,k,l,(K:ℝ)*π+2*π*d,hpb.trans_le hb,by omega,?_,?_⟩
  · intro i
    have hi := i.isLt
    have H := hfirst (p+i.val) (by omega) (by omega)
    rw [hshift] at H
    rwa [show 2*π*liftSite hN x (p+i.val)-((K:ℝ)*π+2*π*d) =
      (2*π*liftSite hN x (p+i.val)-2*π*d)-(K:ℝ)*π by ring]
  · intro j
    have hj := j.isLt
    have H := hlast (p+(2*k+1)+j.val) (by omega) (by omega)
    rw [hshift] at H
    rwa [show 2*π*liftSite hN x (p+(2*k+1)+j.val)-((K:ℝ)*π+2*π*d+π) =
      (2*π*liftSite hN x (p+(2*k+1)+j.val)-2*π*d)-((K+1:ℤ):ℝ)*π by push_cast; ring]

#print axioms groundState_localized_cut

end GaussianChains.Clusters
