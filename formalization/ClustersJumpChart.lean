import ClustersJumpSites
import ClustersJumpSplit

/-! Cutting the genuine cyclic sequence at the change of nearest endpoint.
The two blocks are odd and all their offsets satisfy the paper's radius. -/
noncomputable section
namespace GaussianChains.JumpLocalization
open Real Finset

private theorem floor_budget {M η : ℝ} (hM : 1 ≤ M) (hη : 0 < η)
    (hs : η ≤ 1 / (2*M*(1+3*π*M^2)^2)) :
    2*M*((1+3*π*M^2)*η) < 2-3*M^2*η^2 := by
  let C := 1+3*π*M^2
  have hM' : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hC : 2 ≤ C := by
    dsimp [C]
    have hM₂ : 1 ≤ M^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (by linarith : 0 ≤ M+1)]
    nlinarith only [pi_gt_three, hM₂, mul_nonneg (sub_nonneg.mpr hM₂) pi_pos.le]
  have hC' : 0 < C := by linarith
  change η ≤ 1 / (2*M*C^2) at hs
  have hts := (le_div_iff₀ (show 0 < 2*M*C^2 by positivity)).mp hs
  have hδ : 2*M*C*η ≤ 1/2 := by
    nlinarith only [hts, mul_nonneg (sub_nonneg.mpr hC) (show 0 ≤ 2*M*C*η by positivity)]
  have hu : M*η ≤ 1/4 := by
    nlinarith only [hδ, mul_nonneg (show 0 ≤ C-1 by linarith) (show 0 ≤ M*η by positivity)]
  have hu₂ := mul_self_le_mul_self (show 0 ≤ M*η by positivity) hu
  change 2*M*(C*η) < _
  nlinarith only [hu₂, hδ]

/-- With the published floor condition, the actual cyclic lifts split
into a contiguous odd block and its contiguous odd complement through the
last gap. The common index K identifies the two adjacent antipodal centers. -/
theorem two_odd_localized_blocks {m : ℕ} {hN : 0 < 2*m} {x : Fin (2*m) → ℝ} {h : ℝ}
    (hx : Feasible hN h x) (hh : 0 < h)
    (hJ : 2 - (structureFactor x 1).re ≤ 3*(m:ℝ)^2*(2*π*h)^2)
    (hsmall : 2*π*h ≤ 1 / (2*(m:ℝ)*(1+3*π*(m:ℝ)^2)^2)) :
    ∃ a b k l : ℕ, ∃ K : ℤ, a < b ∧ b ≤ 2*m ∧
      b-a=2*k+1 ∧ 2*m-(b-a)=2*l+1 ∧ k+l+1=m ∧
      (∀ j, a ≤ j → j < b →
        |siteAngle hN x j - (K:ℝ)*π| ≤ (1+3*π*(m:ℝ)^2)*(2*π*h)) ∧
      (∀ j, b ≤ j → j < 2*m+a →
        |siteAngle hN x j - ((K+1:ℤ):ℝ)*π| ≤ (1+3*π*(m:ℝ)^2)*(2*π*h)) := by
  let θ := siteAngle hN x
  let v := endpointIndex θ
  let δ := (1+3*π*(m:ℝ)^2)*(2*π*h)
  have hnear (j : ℕ) (hj : j < 2*m) : |θ j - (v j : ℝ)*π| ≤ δ := by
    obtain ⟨w, hw⟩ := localized_sites hx hh hJ ⟨j, hj⟩
    refine (endpointIndex_nearest θ j w).trans ?_
    change |2*π*liftSite hN x j - (w:ℝ)*π| ≤ _
    rwa [(liftSite_fin hN x ⟨j,hj⟩ : liftSite hN x j = _)]
  have hM : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hδ : ((2*m:ℕ):ℝ)*δ < (structureFactor x 1).re := by
    have h := floor_budget hM (show 0 < 2*π*h by positivity) hsmall
    dsimp [δ]
    push_cast
    linarith only [h,hJ]
  have hper (n : ℕ) : θ (n+2*m) = θ n + 2*π := siteAngle_period hN x n
  have hp : θ (2*m) = θ 0 + 2*π := by simpa using hper 0
  have hcos : ∑ j ∈ range (2*m), (-1:ℝ)^j*cos (θ j) = (structureFactor x 1).re := by
    have h := sum_gapCost θ m hp
    rw [sum_gapCost_eq_deficit hN x] at h
    linarith only [h]
  have ne : (∑ j ∈ range (2*m), (-1:ℝ)^j*cos ((v j:ℝ)*π)) ≠ 0 := by
    intro hz
    have herr := roundedMoment_error θ hnear
    change |(∑ j ∈ range (2*m), (-1:ℝ)^j*cos (θ j)) -
      (∑ j ∈ range (2*m), (-1:ℝ)^j*cos ((v j:ℝ)*π))| ≤ ((2*m:ℕ):ℝ)*δ at herr
    rw [hcos, hz, sub_zero] at herr
    exact (not_le.mpr hδ) ((le_abs_self _).trans herr)
  have hθ : Monotone θ := monotone_nat_of_le_succ (fun n => by
    have hg := siteAngle_gap_floor hx n
    change _ ≤ θ (n+1) - θ n at hg
    linarith [show 0 < 2*π*h by positivity])
  have hv (n : ℕ) : v (n+2*m) = v n + 2 := endpointIndex_period hper n
  obtain ⟨a,b,hab,hb,hod,hleft,hmid,hright⟩ :=
    odd_middle_level v (endpointIndex_monotone hθ) (by simpa using hv 0) ne
  let K := v 0 + 1
  refine ⟨a,b,(b-a)/2,(2*m-(b-a))/2,K,by omega,hb,by omega,by omega,by omega,?_,?_⟩
  · intro j hja hjb
    have h := hnear j (by omega)
    rwa [hmid j hja hjb] at h
  · intro j hjb hja
    have hK : K+1 = v 0+2 := by dsimp [K]; omega
    rw [hK]
    by_cases hj : j < 2*m
    · have h := hnear j hj
      rwa [hright j hjb hj.le] at h
    · let r := j-2*m
      have hra : r < a := by dsimp [r]; omega
      have hjr : j = r+2*m := by dsimp [r]; omega
      have h := hnear r (by omega)
      rw [hleft r hra] at h
      change |θ j - _| ≤ δ
      rw [hjr, hper]
      rw [show θ r + 2*π - ((v 0+2:ℤ):ℝ)*π = θ r - (v 0:ℝ)*π by push_cast; ring]
      exact h

end GaussianChains.JumpLocalization
