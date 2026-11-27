import ClustersContactDerivative
import ClustersContactFeasible
import ClustersSelectionPhysical

noncomputable section
namespace GaussianChains.Clusters

open Real OddBlock AlternatingMoments Finset

private theorem moment_fin (k : ℕ) (u : ℕ → ℝ) :
    ∑ i : Fin (2*k+1), charge i*u i.val = altSum u k :=
  Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i*u i) _

/-- The positive first variation for an actual internal angular gap of a
joined physical cell. The other block remains stationary. -/
theorem joined_gap_derivative {k l p : ℕ} (u v : ℕ → ℝ) {q C η : ℝ}
    (hq : 0 ≤ q) (hq' : q<1) (hR : widthR q ≤ 2/3)
    (hC : 1 ≤ C) (hη : 0 < η)
    (hsmall : η ≤ 1 / ((((2*k+1:ℕ):ℝ)+((2*l+1:ℕ):ℝ))*C^2))
    (hu : ∀ i < 2*k+1, |u i| ≤ C*η) (hv : ∀ i < 2*l+1, |v i| ≤ C*η)
    (hg : ∀ i < 2*k, η ≤ u (i+1)-u i) (hp : 0<p) (hp' : p ≤ 2*k) :
    ∃ dF > 0, HasDerivAt (fun t => 2*(angularK q 0-angularK q π) -
      angularScore q (joinedSites k l (varyGap u p t) v)) dF 0 := by
  let x (i : Fin (2*k+1)) := u i.val
  let vx (i : Fin (2*k+1)) := gapVelocity p i.val
  let y (i : Fin (2*l+1)) := v i.val
  have first (t : ℝ) : (∑ i, charge i*(x i+t*vx i)) = ∑ i, charge i*x i := by
    simp only [x,vx,← varyGap_affine, moment_fin, varied_first_moment u hp hp']
  obtain ⟨dV,hv₁,hv₂⟩ := variance_path_derivative u hp hp' hη.le hg
  have hdV : HasDerivAt (fun t : ℝ => (∑ i, charge i*(x i+t*vx i)^2) -
        (∑ i, charge i*(x i+t*vx i))^2) dV 0 := by
    convert hv₂ using 1
    funext t
    simp only [x,vx,← varyGap_affine, moment_fin]
    rw [moment_fin k (fun i => (varyGap u p t i)^2)]
  have habs {n : ℕ} (i : Fin n) : |charge i|=1 := by simp [charge,abs_pow]
  have hcN : 0 < (Fintype.card (Fin (2*k+1)):ℝ)+(Fintype.card (Fin (2*l+1)):ℝ) := by
    simp only [Fintype.card_fin]
    positivity
  obtain ⟨d,hd,hd'⟩ := contact_derivative_pos charge charge x vx y hq hq' hR
    (odd_charge_sum k) (odd_charge_sum l) habs habs hC hη hcN
    (by simpa only [Fintype.card_fin] using hsmall) (fun i => hu _ i.isLt) (fun j => hv _ j.isLt)
    (fun i => (gapVelocity_bound p i.val 0).1) (fun i j => (gapVelocity_bound p i.val j.val).2)
    first hdV hv₁
  refine ⟨d,hd,?_⟩
  convert hd' using 1
  funext t
  unfold joinedSites
  rw [joined_angularScore]
  simp only [varyGap_affine,x,vx,y]
  ring

theorem joined_score_swap (k l : ℕ) (u v : ℕ → ℝ) (q : ℝ) :
    angularScore q (joinedSites k l u v) = angularScore q (joinedSites l k v u) := by
  unfold joinedSites
  rw [joined_angularScore,joined_angularScore]
  have hcross (x y : ℝ) : angularK q (π+(y-x)) = angularK q (π+(x-y)) := by
    unfold angularK
    rw [show π+(y-x) = π-(x-y) by ring, angularCos_pi_reflect]
  unfold blockSum
  rw [sum_comm (f := fun (i : Fin (2*l+1)) (j : Fin (2*k+1)) =>
    charge i*charge j*angularK q (π+(v i.val-u j.val)))]
  simp_rw [mul_comm (charge (_ : Fin (2*l+1))) (charge (_ : Fin (2*k+1))), hcross (u _) (v _)]
  ring

/-- Exact contact in both odd blocks of every minimizing cell in the
localized chart. The only geometric input is a bound on each site's offset
from its assigned antipode. -/
theorem localized_groundState_contacts {k l : ℕ} (u v : ℕ → ℝ) {s h C : ℝ}
    (hs : 0<s) (hh : 0<h) (hC : 1 ≤ C)
    (hR : widthR (exp (-(π^2)/s)) ≤ 2/3)
    (hsmall : 2*π*h ≤ 1 / ((((2*k+1:ℕ):ℝ)+((2*l+1:ℕ):ℝ))*C^2))
    (hu : ∀ i < 2*k+1, |u i| ≤ C*(2*π*h)) (hv : ∀ i < 2*l+1, |v i| ≤ C*(2*π*h))
    (hmin : IsGroundState (by omega) h s (joinedSites k l u v)) :
    (∀ i < 2*k, u (i+1)-u i = 2*π*h) ∧ (∀ j < 2*l, v (j+1)-v j = 2*π*h) := by
  let q := exp (-(π^2)/s)
  have hq : 0 ≤ q := (exp_pos _).le
  have hq' : q < 1 := exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos pi_pos)) hs)
  obtain ⟨hg₁,hg₂,_⟩ := (joinedBlocks_feasible_iff k l u v h).1 hmin.1
  have hη : 0<2*π*h := by positivity
  constructor
  · intro i hi
    obtain ⟨d,hd,hf⟩ := joined_gap_derivative u v hq hq' hR hC hη hsmall hu hv hg₁
      (p := i+1) (by omega) (by omega)
    exact groundState_left_gap_tight hs hmin (Nat.succ_pos i) (by omega) hf hd
  · intro j hj
    obtain ⟨d,hd,hf⟩ := joined_gap_derivative v u hq hq' hR hC hη
      (by rwa [add_comm]) hv hu hg₂ (p := j+1) (by omega) (by omega)
    simp_rw [joined_score_swap l k _ u] at hf
    exact groundState_right_gap_tight hs hmin (Nat.succ_pos j) (by omega) hf hd

end GaussianChains.Clusters
