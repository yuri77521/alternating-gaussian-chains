import ClustersMidpoint
import ClustersSelectionKernel

/-! After contact locking the remaining variable is the separation π+v
between the actual midpoints. The comparison is on the segment from -|v|
to |v|, including the centered trial. -/
noncomputable section
namespace GaussianChains.Clusters
open Real

private theorem angularK_reflect (q z : ℝ) :
    angularK q (π + -z) = angularK q (π + z) := by
  simpa only [sub_eq_add_neg] using angularCos_pi_reflect 0 q z

/-- Moving one packed block rigidly changes only the two cross interactions.
Here the first block is translated by angular distance `v` relative to the
second. Charges in the second block have been normalized to start at +1,
as in the definition of the deficit. -/
theorem packed_cross_eq_blockSum (k l : ℕ) (η v : ℝ) (K : ℝ → ℝ) :
    packedCross k l η K v =
      2*blockSum (@packedSign k) (@packedSign l) (fun i => v+packedOffset η i)
        (packedOffset η) K π := by
  unfold packedCross blockSum
  simp only [add_sub_assoc]

/-- The two outer angular gaps of a packed pair are
`π - (k+l)*η ± v`. Feasibility of both endpoints implies that every
intermediate displacement, in particular zero, respects the same floor. -/
theorem packed_outer_gaps_on_segment {b η v z : ℝ} (h₁ : η ≤ b+v) (h₂ : η ≤ b-v)
    (hz : z ∈ Set.Icc (-|v|) |v|) : η ≤ b+z ∧ η ≤ b-z := by
  rcases abs_cases v with ⟨hv, _⟩ | ⟨hv, _⟩ <;> rw [hv] at hz <;>
    constructor <;> linarith [hz.1, hz.2]

private theorem packed_pair_budget {a b C η : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : 0 < C) (hη : 0 ≤ η) (hsmall : η ≤ 1/((a+b)*C^2)) :
    2*a*b*(2*C*η)^2 ≤ 2/C^2 := by
  have hs := (le_div_iff₀ (show 0 < (a+b)*C^2 by positivity)).mp hsmall
  have hs2 : (η*((a+b)*C^2))^2 ≤ 1^2 := pow_le_pow_left₀ (by positivity) hs 2
  apply (le_div_iff₀ (sq_pos_of_pos hC)).mpr
  calc
    _ ≤ 2*(η*((a+b)*C^2))^2 := by
      nlinarith only [mul_nonneg (sq_nonneg (a-b)) (mul_nonneg (sq_nonneg η) (pow_nonneg hC.le 4))]
    _ ≤ 2 := by linarith only [hs2]

theorem packedCross_kernel_curvature (k l : ℕ) {q η C v : ℝ}
    (hq : 0 ≤ q) (hq' : q < 1) (hR : widthR q ≤ 2/3) (hC : 2 ≤ C) (hη : 0 ≤ η)
    (hsmall : η ≤ 1/((((2*k+1 : ℕ) : ℝ)+((2*l+1 : ℕ) : ℝ))*C^2))
    (hloc : ∀ (i : Fin (2*k+1)) (j : Fin (2*l+1)),
      |v + (packedOffset η i - packedOffset η j)| ≤ 2*C*η) :
    2*(-angularCos 2 q π) - 2/C^2 ≤ deriv (deriv (packedCross k l η (angularK q))) v := by
  let D := fun x => -angularSin 1 q x
  let D₂ := fun x => -angularCos 2 q x
  have dK (x : ℝ) : HasDerivAt (angularK q) (D x) x := angularCos_hasDerivAt hq hq' 0 x
  have dD (x : ℝ) : HasDerivAt D (D₂ x) x := (angularSin_hasDerivAt hq hq' 1 x).neg
  have dF : deriv (packedCross k l η (angularK q)) = packedCross k l η D :=
    funext fun t => (packedCross_hasDerivAt k l η dK t).deriv
  rw [dF, (packedCross_hasDerivAt k l η dD v).deriv]
  have hterm (i : Fin (2*k+1)) (j : Fin (2*l+1)) :
      |D₂ (π + (v + (packedOffset η i - packedOffset η j))) - (-angularCos 2 q π)| ≤
        (2*C*η)^2 := by
    rw [sub_neg_eq_add]
    exact (angular_taylor_bounds hq hq' hR (Or.inr rfl) _).1.trans
      (pow_le_pow_left₀ (abs_nonneg _) (hloc i j) 2)
  have hp := packedCross_error k l η D₂ v (-angularCos 2 q π) ((2*C*η)^2) hterm
  have budget := packed_pair_budget (a := ((2*k+1 : ℕ) : ℝ)) (b := ((2*l+1 : ℕ) : ℝ))
    (by positivity) (by positivity) (by linarith) hη hsmall
  linarith only [(abs_le.mp hp).1, budget]

/-- Every localized packed candidate no worse than its centered competitor
must itself have antipodal midpoints. The sole comparison assumption is
between two specified physical shapes on the same packed contact face. -/
theorem packed_midpoint_locked (k l : ℕ) {q η C v : ℝ}
    (hq : 0 ≤ q) (hq' : q < 1) (hR : widthR q ≤ 2/3) (hC : 2 ≤ C) (hη : 0 ≤ η)
    (hsmall : η ≤ 1/((((2*k+1 : ℕ) : ℝ)+((2*l+1 : ℕ) : ℝ))*C^2))
    (hloc : ∀ (i : Fin (2*k+1)) (j : Fin (2*l+1)),
      |v + (packedOffset η i - packedOffset η j)| ≤ 2*C*η)
    (hmin : packedCross k l η (angularK q) v ≤ packedCross k l η (angularK q) 0) : v = 0 := by
  apply midpoint_eq_zero_of_min (r := |v|) (f := packedCross k l η (angularK q))
    (Kπ := -angularCos 2 q π) (C := C) ⟨neg_abs_le _, le_abs_self _⟩
    (packedCross_even k l η (angularK_reflect q) v)
  · intro x _
    exact (packedCross_hasDerivAt k l η (angularCos_hasDerivAt hq hq' 0) x).continuousAt.continuousWithinAt
  · exact (locking_curvature_bounds hq hq' hR π).2.2
  · exact hC
  · intro z hz
    exact packedCross_kernel_curvature k l hq hq' hR hC hη hsmall
      (packed_segment_localized hloc (interior_subset hz))
  · exact hmin

#print axioms packed_midpoint_locked
end GaussianChains.Clusters

