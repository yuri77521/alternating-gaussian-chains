import PackedFaceBoundsThresholdAnalytic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Implicit derivatives for the two simple endpoint zeros, with respect to the nome. -/
noncomputable section
namespace GaussianChains.PackedFace
open Filter Set Real
open scoped Topology

private theorem hasDerivAt_implicit_zero {P : ℝ × ℝ → ℝ} {r : ℝ → ℝ} {q : ℝ}
    (hP : DifferentiableAt ℝ P (q,r q)) (hr : DifferentiableAt ℝ r q)
    (hz : (fun t => P (t,r t)) =ᶠ[𝓝 q] fun _ => (0 : ℝ))
    (hn : deriv (fun h => P (q,h)) (r q) ≠ 0) :
    HasDerivAt r (-deriv (fun t => P (t,r q)) q / deriv (fun h => P (q,h)) (r q)) q := by
  let D := fderiv ℝ P (q,r q)
  have hD : HasFDerivAt P D (q,r q) := hP.hasFDerivAt
  have dq : HasDerivAt (fun t => P (t,r q)) (D (1,0)) q :=
    hD.comp_hasDerivAt q ((hasDerivAt_id q).prodMk (hasDerivAt_const q (r q)))
  have dh : HasDerivAt (fun u => P (q,u)) (D (0,1)) (r q) :=
    hD.comp_hasDerivAt (r q) ((hasDerivAt_const (r q) q).prodMk (hasDerivAt_id (r q)))
  have dr : HasDerivAt (fun t => P (t,r t)) (D (1,deriv r q)) q :=
    hD.comp_hasDerivAt q ((hasDerivAt_id q).prodMk hr.hasDerivAt)
  have h0 : D (1,deriv r q) = 0 := dr.deriv.symm.trans (hz.deriv_eq.trans (deriv_const q 0))
  have hadd : D (1,deriv r q) = D (1,0) + deriv r q * D (0,1) := calc
    D (1,deriv r q) = D ((1,0) + deriv r q • (0,1)) := by congr 1; ext <;> simp
    _ = _ := by rw [map_add, map_smul, smul_eq_mul]
  have hval : deriv r q = -deriv (fun t => P (t,r q)) q / deriv (fun h => P (q,h)) (r q) := by
    apply (eq_div_iff hn).2
    rw [dq.deriv, dh.deriv]
    linarith
  rw [← hval]
  exact hr.hasDerivAt

private theorem criticalFloor_hasDerivAt_ratio (outer : Bool) {q : ℝ}
    (hq : 0 < q) (hQ : q < faceQ) :
    HasDerivAt (criticalFloor outer)
      (-deriv (fun t => floorSlope outer t (criticalFloor outer q)) q /
        deriv (floorSlope outer q) (criticalFloor outer q)) q := by
  have hlocal : (fun t => floorSlope outer t (criticalFloor outer t)) =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
    filter_upwards [Ioc_mem_nhds hq hQ] with t ht
    exact (criticalFloor_spec outer ht.1 ht.2).2.1
  exact hasDerivAt_implicit_zero (P := fun p => floorSlope outer p.1 p.2)
    ((floorSlope_contDiffAt outer ⟨hq,hQ.le⟩ _).differentiableAt (by decide))
    (criticalFloor_analyticAt outer ⟨hq,hQ⟩).differentiableAt hlocal
    (criticalFloor_spec outer hq hQ.le).2.2.1

/-- The numerator is the full Gaussian series of differentiated endpoint modes. -/
theorem criticalFloor_hasDerivAt (outer : Bool) {q : ℝ} (hq : 0 < q) (hQ : q < faceQ) :
    HasDerivAt (criticalFloor outer)
      (-(∑' k : ℕ, endpointDq (k+1) q (cos (2*π*criticalFloor outer q))
        (endpointZ outer (cos (2*π*criticalFloor outer q)))) /
        deriv (floorSlope outer q) (criticalFloor outer q)) q := by
  have hh := (criticalFloor_spec outer hq hQ.le).1
  have hr := z_range outer (cos_floor_large hh.1.le hh.2.le)
  have hd := (endpointSlope_hasDerivAt_q hq hQ.le hr.1 hr.2).deriv
  simpa only [floorSlope, hd] using criticalFloor_hasDerivAt_ratio outer hq hQ

theorem criticalFloor_deriv_neg (outer : Bool) {q : ℝ} (hq : 0 < q) (hQ : q < faceQ) :
    deriv (criticalFloor outer) q < 0 := by
  have hh := (criticalFloor_spec outer hq hQ.le).1
  have hx := cos_floor_large hh.1.le hh.2.le
  have hr := z_range outer hx
  have ha := x_transition_data hx outer
  have hnum := endpointSlope_dq_neg hq hQ.le hr.1 hr.2 ha.2.1 ha.2.2.1.1
  have hden := floorSlope_deriv_neg outer hq hQ.le hh
  rw [(criticalFloor_hasDerivAt_ratio outer hq hQ).deriv]
  exact div_neg_of_pos_of_neg (neg_pos.mpr hnum) hden

end GaussianChains.PackedFace

