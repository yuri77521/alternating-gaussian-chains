import PackedFaceSlopesBounds
import PackedFaceBoundsEndpoints
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Differentiation of the endpoint series on the transition interval. -/
noncomputable section
namespace GaussianChains.PackedFace
open Set

private theorem wt_summable {q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ) (p : ℕ) (hp : p = 2 ∨ p = 4) :
    Summable (fun k : ℕ => weightedMode q p (k+1)) := by
  obtain rfl | rfl := hp
  · exact (summable_nat_add_iff (f := fun k => weightedMode q 2 (k+1)) 3).mp
      (by simpa only [Nat.add_assoc] using (second_tail_bound hq hQ).1)
  · exact (summable_nat_add_iff (f := fun k => weightedMode q 4 (k+1)) 2).mp
      (by simpa only [Nat.add_assoc] using (fourth_tail_bound hq hQ).1)

theorem endpointMode_summable {q x z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Icc (-1) 1) (hz : z ∈ Icc (-1) 1) :
    Summable (fun k : ℕ => endpointMode (k+1) q x z) :=
  Summable.of_norm_bounded ((wt_summable hq hQ 2 (.inl rfl)).mul_left 9) (fun k => by
    simpa [Real.norm_eq_abs] using endpointMode_bound (k+1) hq hx hz)

theorem endpointSlope_eq_head_tail {q x z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Icc (-1) 1) (hz : z ∈ Icc (-1) 1) :
    endpointSlope q x z = slopeHead q x z + ∑' k : ℕ, endpointMode (k+3) q x z := by
  have h := ((endpointMode_summable hq hQ hx hz).sum_add_tsum_nat_add 2).symm
  change (∑' k : ℕ, endpointMode (k+1) q x z) = _
  simpa [Finset.sum_range_succ, Nat.add_assoc, endpointMode_one_two, slopeHead] using h

/-- The derivative with respect to x is the sum of all differentiated modes
on the open part of any endpoint path staying inside the Chebyshev domain. -/
theorem endpointSlope_hasDerivAt_x {q a b x : ℝ} {z dz : ℝ → ℝ}
    (hq : 0 ≤ q) (hQ : q ≤ faceQ) (hx : x ∈ Ioo a b)
    (hrange : ∀ v ∈ Ioo a b, v ∈ Icc (-1) 1 ∧ z v ∈ Icc (-1) 1)
    (hpath : ∀ v ∈ Ioo a b, HasDerivAt z (dz v) v ∧ |dz v| ≤ 3) :
    HasDerivAt (fun v => endpointSlope q v (z v))
      (∑' k : ℕ, endpointDx (k+1) q x (z x) (dz x)) x := by
  have hw := (wt_summable hq hQ 4 (.inr rfl)).mul_left 39
  exact hasDerivAt_tsum_of_isPreconnected hw isOpen_Ioo isPreconnected_Ioo
    (fun k v hv => endpointMode_hasDerivAt_x (k+1) q v (dz v) (hpath v hv).1)
    (fun k v hv => by simpa [Real.norm_eq_abs] using
      endpointDx_bound (n:=k+1) (by omega) hq (hrange v hv).1 (hrange v hv).2 (hpath v hv).2)
    hx (endpointMode_summable hq hQ (hrange x hx).1 (hrange x hx).2) hx

private theorem derivative_head_eq {x q dz : ℝ} {z : ℝ → ℝ} (hz : HasDerivAt z dz x) :
    endpointDx 1 q x (z x) dz + endpointDx 2 q x (z x) dz =
      4*(2*x-1) + 64*q^3*x*(3-4*x^2)*z x - 4*q^3*(4*x^2-3)^2*dz := by
  have hs := (endpointMode_hasDerivAt_x 1 q x dz hz).add (endpointMode_hasDerivAt_x 2 q x dz hz)
  have he : (fun t => endpointMode 1 q t (z t) + endpointMode 2 q t (z t)) =
      fun t => slopeHead q t (z t) := funext (fun t => endpointMode_one_two q t (z t))
  change HasDerivAt (fun t => endpointMode 1 q t (z t) + endpointMode 2 q t (z t)) _ _ at hs
  rw [he] at hs
  exact hs.unique (slopeHead_hasDerivAt_x q x dz z hz)

/-- Strict total x derivative of the actual infinite endpoint slope. The
hypotheses on the path are shared by the constant and cubic endpoints. -/
theorem endpointSlope_dx_pos {q a b x : ℝ} {z dz : ℝ → ℝ}
    (hq : 0 < q) (hQ : q ≤ faceQ) (hx : x ∈ Ioo a b)
    (hrange : ∀ v ∈ Ioo a b, v ∈ Icc (-1) 1 ∧ z v ∈ Icc (-1) 1)
    (hpath : ∀ v ∈ Ioo a b, HasDerivAt z (dz v) v ∧ |dz v| ≤ 3)
    (hx0 : 1/2 ≤ x) (hx1 : x^2 ≤ 1/2) (hz0 : 1/2 ≤ z x) (hdz : dz x ≤ 0) :
    0 < deriv (fun v => endpointSlope q v (z v)) x := by
  rw [(endpointSlope_hasDerivAt_x hq.le hQ hx hrange hpath).deriv]
  have ⟨hs,ht⟩ := endpointDx_tail hq.le hQ (hrange x hx).1 (hrange x hx).2 (hpath x hx).2
  have hsum : Summable (fun k : ℕ => endpointDx (k+1) q x (z x) (dz x)) :=
    (summable_nat_add_iff 2).mp (by simpa only [Nat.add_assoc] using hs)
  rw [← hsum.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd, Nat.add_assoc]
  rw [derivative_head_eq (hpath x hx).1]
  have hl := slopeHead_dx_lower hq.le hx0 hx1 hz0 hdz
  have hb := (abs_le.mp ht).1
  have hconst := face_constant_bounds.2.2.1
  nlinarith only [hl, hb, mul_pos (pow_pos hq 3) (sub_pos.mpr hconst)]

private theorem summable_neighborhood_weight :
    Summable (fun k : ℕ => weightedMode (1/2) 4 (k+1)) :=
  (summable_nat_add_iff 2).mp (by
    simpa only [Nat.add_assoc] using (weightedMode_tail (q:=1/2) (Q:=1/2)
      (by norm_num) le_rfl (by norm_num) 4 3 (by decide) (by norm_num [tailRatio])).1)

private theorem dq_majorant {q v x z : ℝ} {k : ℕ} (hq : 0 < q)
    (hv : v ∈ Ioo (q/2) (1/2)) (hx : x ∈ Icc (-1) 1) (hz : z ∈ Icc (-1) 1) :
    ‖endpointDq (k+1) v x z‖ ≤ (18/q)*weightedMode (1/2) 4 (k+1) := by
  rcases k with _|k
  · simp [endpointDq, weightedMode] <;> positivity
  · have hv0 : 0 < v := lt_trans (by positivity) hv.1
    have hs := endpointDq_scaled_bound (n:=k+1+1) (by omega) hv0.le hx hz
    rw [abs_mul, abs_of_pos hv0] at hs
    have hw : weightedMode v 4 (k+1+1) ≤ weightedMode (1/2) 4 (k+1+1) := by
      unfold weightedMode
      gcongr
      exact hv.2.le
    rw [Real.norm_eq_abs, div_mul_eq_mul_div, le_div_iff₀ hq]
    nlinarith only [hs, hw, mul_nonneg (sub_nonneg.mpr hv.1.le)
      (abs_nonneg (endpointDq (k+1+1) v x z))]

/-- A slightly larger parameter neighborhood gives the ordinary derivative
also at q=17/50. Only the value of its majorant at the point uses the sharp
constant of the manuscript. -/
theorem endpointSlope_hasDerivAt_q {q x z : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (hx : x ∈ Icc (-1) 1) (hz : z ∈ Icc (-1) 1) :
    HasDerivAt (fun v => endpointSlope v x z) (∑' k : ℕ, endpointDq (k+1) q x z) q := by
  have hmem : q ∈ Ioo (q/2) (1/2 : ℝ) :=
    ⟨by linarith, lt_of_le_of_lt hQ (by norm_num [faceQ])⟩
  exact hasDerivAt_tsum_of_isPreconnected (summable_neighborhood_weight.mul_left (18/q))
    isOpen_Ioo isPreconnected_Ioo (fun k v _ => endpointMode_hasDerivAt_q (k+1) v x z)
    (fun _ v hv => dq_majorant hq hv hx hz) hmem (endpointMode_summable hq.le hQ hx hz) hmem

private theorem derivative_head_eq_q (q x z : ℝ) :
    endpointDq 1 q x z + endpointDq 2 q x z = -(12*q^2*(4*x^2-3)^2*z) := by
  have hs := (endpointMode_hasDerivAt_q 1 q x z).add (endpointMode_hasDerivAt_q 2 q x z)
  have he : (fun t => endpointMode 1 t x z + endpointMode 2 t x z) =
      fun t => slopeHead t x z := funext (fun t => endpointMode_one_two t x z)
  change HasDerivAt (fun t => endpointMode 1 t x z + endpointMode 2 t x z) _ _ at hs
  rw [he] at hs
  exact hs.unique (slopeHead_hasDerivAt_q q x z)

theorem endpointSlope_dq_neg {q x z : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ)
    (hx : x ∈ Icc (-1) 1) (hz : z ∈ Icc (-1) 1) (hx1 : x^2 ≤ 1/2) (hz0 : 1/2 ≤ z) :
    deriv (fun v => endpointSlope v x z) q < 0 := by
  rw [(endpointSlope_hasDerivAt_q hq hQ hx hz).deriv]
  apply neg_of_mul_neg_right (a:=q) _ hq.le
  rw [← tsum_mul_left]
  have ⟨hs,ht⟩ := endpointDq_scaled_tail hq.le hQ hx hz
  have hsum : Summable (fun k : ℕ => q*endpointDq (k+1) q x z) :=
    (summable_nat_add_iff 2).mp (by simpa only [Nat.add_assoc] using hs)
  rw [← hsum.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd, Nat.add_assoc]
  rw [← mul_add, derivative_head_eq_q]
  have hh := slopeHead_qdq_upper hq.le hx1 hz0
  have hb := (abs_le.mp ht).2
  have hconst := face_constant_bounds.2.2.2
  nlinarith only [hh, hb, mul_pos (pow_pos hq 3) (sub_pos.mpr hconst)]

theorem endpointSlope_uniform_neg {q : ℝ} (hq : 0 < q) (hQ : q ≤ faceQ) :
    endpointSlope q (1/2) 1 < 0 := by
  have hx : (1/2 : ℝ) ∈ Icc (-1) 1 := by constructor <;> norm_num
  have hz : (1 : ℝ) ∈ Icc (-1) 1 := by constructor <;> norm_num
  rw [endpointSlope_eq_head_tail hq.le hQ hx hz]
  have h := endpoint_tail_control (f := fun k => endpointMode (k+3) q (1/2) 1) (C:=9)
    hq.le hQ (fun k => by
      have hp : ((k+3:ℕ):ℝ)^2 ≤ ((k+3:ℕ):ℝ)^4 := by
        have : (1:ℝ) ≤ ((k+3:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ k+3 by omega)
        exact pow_le_pow_right₀ this (by decide)
      apply (endpointMode_bound _ hq.le hx hz).trans
      unfold weightedMode
      gcongr) (by norm_num)
  have hb := (abs_le.mp h.2).2
  norm_num [slopeHead]
  nlinarith only [hb, mul_pos (pow_pos hq 3) (sub_pos.mpr face_constant_bounds.2.2.2),
    pow_pos hq 3]

end GaussianChains.PackedFace
