import PackedFaceSlopesDeriv
import PackedFaceSlopesRoots
import PackedFaceSlopeLink
import Mathlib.Topology.Algebra.Polynomial

/-! The two zero tests on the closed floor band. -/
noncomputable section
namespace GaussianChains.PackedFace
open Real Set

/-- The abscissa of the derivative of the Chebyshev polynomial is 1 at the
center and the triple-angle expression at outer contact. -/
def endpointZ (outer : Bool) (x : ℝ) : ℝ :=
  if outer then 3*x-4*x^3 else 1

def endpointZ' (outer : Bool) (x : ℝ) : ℝ :=
  if outer then 3-12*x^2 else 0

def floorSlope (outer : Bool) (q h : ℝ) : ℝ :=
  endpointSlope q (cos (2*π*h)) (endpointZ outer (cos (2*π*h)))

private theorem endpointZ_deriv (outer : Bool) (x : ℝ) :
    HasDerivAt (endpointZ outer) (endpointZ' outer x) x := by
  cases outer
  · simpa [endpointZ,endpointZ'] using hasDerivAt_const x (1:ℝ)
  · simpa [endpointZ,endpointZ'] using cubic_endpoint_hasDerivAt x

theorem x_transition_data {x : ℝ} (hx : x ∈ Icc (1/2) (√2/2)) (outer : Bool) :
    x ∈ Icc (-1) 1 ∧ x^2 ≤ 1/2 ∧ endpointZ outer x ∈ Icc (1/2) 1 ∧
    endpointZ' outer x ∈ Icc (-3) 0 := by
  have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hsq : x^2 ≤ 1/2 := by
    nlinarith [mul_self_le_mul_self (by linarith [hx.1] : 0 ≤ x) hx.2]
  refine ⟨⟨by linarith [hx.1],by nlinarith [sq_nonneg (x-1)]⟩,hsq,?_⟩
  cases outer
  · norm_num [endpointZ,endpointZ']
  · exact ⟨⟨(large_floor_modes hx.1 hx.2).2.1,(large_floor_modes hx.1 hx.2).2.2.1⟩,
      (large_floor_modes hx.1 hx.2).2.2.2⟩

theorem z_range {x : ℝ} (outer : Bool) (hx : x ∈ Icc (1/2) (√2/2)) :
    x ∈ Icc (-1) 1 ∧ endpointZ outer x ∈ Icc (-1) 1 := by
  obtain ⟨ha,_,hb,_⟩ := x_transition_data hx outer
  exact ⟨ha,⟨le_trans (by norm_num) hb.1,hb.2⟩⟩

theorem z_path {x : ℝ} (outer : Bool) (hx : x ∈ Icc (1/2) (√2/2)) :
    HasDerivAt (endpointZ outer) (endpointZ' outer x) x ∧ |endpointZ' outer x| ≤ 3 := by
  have hd := (x_transition_data hx outer).2.2.2
  exact ⟨endpointZ_deriv outer x,abs_le.mpr ⟨hd.1,le_trans hd.2 (by norm_num)⟩⟩

theorem continuousOn_floorSlope (outer : Bool) {q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) :
    ContinuousOn (floorSlope outer q) (Icc (1/8) (1/6)) := by
  change ContinuousOn (fun h => ∑' k : ℕ, endpointMode (k+1) q (cos (2*π*h))
    (endpointZ outer (cos (2*π*h)))) _
  refine continuousOn_tsum (fun n => ?_) (u := fun k : ℕ => 9 * weightedMode q 2 (k+1))
    ?_ (fun k h hh => ?_)
  · apply Continuous.continuousOn
    have hz : Continuous (endpointZ outer) := continuous_iff_continuousAt.mpr
      (fun x => (endpointZ_deriv outer x).continuousAt)
    unfold endpointMode modeT modeU
    fun_prop
  · apply Summable.mul_left
    exact (summable_nat_add_iff 3).mp (by simpa only [Nat.add_assoc] using
      (second_tail_bound hq hQ).1)
  · have hr := z_range outer (cos_floor_large hh.1 hh.2)
    simpa [Real.norm_eq_abs] using endpointMode_bound (k+1) hq hr.1 hr.2

theorem cos_floor_mem_open {h : ℝ} (hh : h ∈ Ioo (1/8) (1/6)) :
    cos (2*π*h) ∈ Ioo (1/2) (√2/2) := by
  rw [← Real.cos_pi_div_three, ← Real.cos_pi_div_four]
  have ha : π/4 < 2*π*h := by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hh.1)]
  have hb : 2*π*h < π/3 := by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hh.2)]
  have hc : 2*π*h ∈ Icc 0 π := ⟨by linarith [pi_pos],by linarith [pi_pos]⟩
  exact ⟨strictAntiOn_cos hc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ hb,
    strictAntiOn_cos ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ hc ha⟩

/-- Factorization of the floor derivative for the phase-width comparison. -/
theorem floorSlope_deriv_eq (outer : Bool) {q h : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hh : h ∈ Ioo (1/8) (1/6)) :
    deriv (floorSlope outer q) h =
      deriv (fun x => endpointSlope q x (endpointZ outer x)) (cos (2*π*h)) *
        (-sin (2*π*h) * (2*π)) := by
  have hx := cos_floor_mem_open hh
  have hrange := fun v (hv : v ∈ Ioo (1/2:ℝ) (√2/2)) => z_range outer (Ioo_subset_Icc_self hv)
  have hpath := fun v (hv : v ∈ Ioo (1/2:ℝ) (√2/2)) => z_path outer (Ioo_subset_Icc_self hv)
  have hder := endpointSlope_hasDerivAt_x hq hQ hx hrange hpath
  exact (hasDerivAt_slope_in_floor hder.differentiableAt.hasDerivAt).deriv

theorem floorSlope_deriv_neg (outer : Bool) {q h : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (hh : h ∈ Ioo (1/8) (1/6)) :
    deriv (floorSlope outer q) h < 0 := by
  let x := cos (2*π*h)
  have hx : x ∈ Ioo (1/2) (√2/2) := cos_floor_mem_open hh
  have hrange := fun v (hv : v ∈ Ioo (1/2:ℝ) (√2/2)) => z_range outer (Ioo_subset_Icc_self hv)
  have hpath := fun v (hv : v ∈ Ioo (1/2:ℝ) (√2/2)) => z_path outer (Ioo_subset_Icc_self hv)
  have hdata := x_transition_data (Ioo_subset_Icc_self hx) outer
  have hd := endpointSlope_dx_pos hq hQ hx hrange hpath hx.1.le hdata.2.1 hdata.2.2.1.1 hdata.2.2.2.2
  have h := endpointSlope_hasDerivAt_x hq.le hQ hx hrange hpath
  exact slope_in_floor_deriv_neg (Ioo_subset_Icc_self hh) hd h.differentiableAt.hasDerivAt

theorem floorSlope_unique_root (outer : Bool) {q : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ) :
    ∃ r ∈ Ioo (1/8) (1/6), floorSlope outer q r = 0 ∧ deriv (floorSlope outer q) r ≠ 0 ∧
      ∀ h ∈ Icc (1/8) (1/6), floorSlope outer q h = 0 ↔ h = r := by
  apply endpoint_root_of_deriv_neg _ (continuousOn_floorSlope outer hq.le hQ)
    (fun _ h => floorSlope_deriv_neg outer hq hQ h)
  · rcases inner_endpoint_slopes_pos hq.le hQ with ⟨h₁,h₂⟩
    cases outer
    · exact h₁
    · rw [outer_abscissa] at h₂
      exact h₂
  · have hc : cos (2*π*(1/6)) = 1/2 := by
      rw [show 2*π*(1/6) = π/3 by ring, cos_pi_div_three]
    unfold floorSlope
    rw [hc]
    cases outer <;> norm_num [endpointZ] <;> exact endpointSlope_uniform_neg hq hQ

def criticalFloor (outer : Bool) (q : ℝ) : ℝ :=
  if hq : 0 < q ∧ q ≤ faceQ then (floorSlope_unique_root outer hq.1 hq.2).choose else 0

theorem criticalFloor_spec (outer : Bool) {q : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ) :
    criticalFloor outer q ∈ Ioo (1/8) (1/6) ∧ floorSlope outer q (criticalFloor outer q) = 0 ∧
    deriv (floorSlope outer q) (criticalFloor outer q) ≠ 0 ∧ ∀ h ∈ Icc (1/8) (1/6),
      floorSlope outer q h = 0 ↔ h = criticalFloor outer q := by
  simpa [criticalFloor, hq, hQ] using (floorSlope_unique_root outer hq hQ).choose_spec

theorem criticalFloor_strictAntiOn (outer : Bool) :
    StrictAntiOn (criticalFloor outer) (Ioc 0 faceQ) := by
  refine strictAntiOn_endpoint_roots (P:=floorSlope outer) (H:=Icc (1/8) (1/6))
    (fun q hq => Ioo_subset_Icc_self (criticalFloor_spec outer hq.1 hq.2).1)
    (fun q hq => (criticalFloor_spec outer hq.1 hq.2).2.1) ?_ ?_
  · intro h hh
    have hz := z_range outer (cos_floor_large hh.1 hh.2)
    have hdata := x_transition_data (cos_floor_large hh.1 hh.2) outer
    apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    · intro q hq
      exact (endpointSlope_hasDerivAt_q hq.1 hq.2 hz.1 hz.2).continuousAt.continuousWithinAt
    · intro q hq
      have hmem : q ∈ Ioc (0:ℝ) faceQ := interior_subset hq
      exact endpointSlope_dq_neg hmem.1 hmem.2 hz.1 hz.2 hdata.2.1 hdata.2.2.1.1
  · intro q hq
    exact strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuousOn_floorSlope outer hq.1.le hq.2)
      (by simpa only [interior_Icc] using fun h (hh : h ∈ Ioo (1/8:ℝ) (1/6)) =>
        floorSlope_deriv_neg outer hq.1 hq.2 hh)

theorem criticalFloor_width_strictAntiOn (outer : Bool) :
    StrictAntiOn (fun s => criticalFloor outer (exp (-(π^2)/s)))
      {s : ℝ | 0 < s ∧ exp (-(π^2)/s) ≤ faceQ} := by
  intro s hs t ht hst
  exact criticalFloor_strictAntiOn outer ⟨exp_pos _,hs.2⟩ ⟨exp_pos _,ht.2⟩
    (nome_strictMonoOn hs.1 ht.1 hst)

end GaussianChains.PackedFace
