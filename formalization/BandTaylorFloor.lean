import BandTaylorBase
import Mathlib.Analysis.Calculus.MeanValue

/-! Bounds for varying the floor about its midpoint and replacing each of the
fifteen midpoint kernel values by a rational sample. -/
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip Finset Interval

private def velocity (c : Center) (p : Pair) : ℚ :=
  (p.2.val - p.1.val : ℕ) - 6 * arcMass c p

private theorem distance_deriv (c : Center) (p : Pair) (w : ℝ) :
    HasDerivAt (fun z => distance z (liftCenter c) p) (velocity c p : ℝ) w := by
  let n := (p.2.val-p.1.val : ℕ)
  let a := ∑ k ∈ arc p.1 p.2, liftCenter c k
  have hv := ((hasDerivAt_id w).const_mul (n:ℝ)).add
    ((((hasDerivAt_id w).const_mul (6:ℝ)).const_sub (1:ℝ)).mul_const a)
  convert hv using 1 <;> simp [velocity,distance,arcMass,liftCenter,n,a] <;> ring

/-- This uses derivative intervals over the full floor interval. -/
theorem floorError_sound {F : ℕ → ℝ → ℝ} {q : Oracle}
    {floor : Interval} {B : Box 6} {c : Center} {h : ℝ}
    (hF : ∀ x, HasDerivAt (F 0) (F 1 x) x) (hq : FirstOracleSound q F)
    (hf : fitFloor floor = true) (hb : B.Mem (liftCenter c)) (hc : simplex (liftCenter c))
    (hh : floor.Mem h) :
    |expression .value F h (liftCenter c) - expression .value F (middle floor) (liftCenter c)| ≤
      (floorError q floor B c : ℝ) := by
  let u := liftCenter c
  let f (w : ℝ) := expression .value F w u
  let D (w : ℝ) := ∑ p ∈ pairs, (coefficient p : ℝ) * (F 1 (distance w u p) * (velocity c p : ℝ))
  have hd (w : ℝ) : HasDerivAt f (D w) w := by
    change HasDerivAt (fun w => expression .value F w u) _ w
    simp_rw [value_eq_sum]
    exact sum_deriv hF (fun p _ => distance_deriv c p w)
  let J := hSlopeBounds q floor B c
  have hJ (w : ℝ) (hw : floor.Mem w) : J.Mem (D w) := by
    apply sumRange_mem
    intro p _
    simpa only [mul_assoc] using
      mul_mem (pairSlope_sound hq hf hw hb hc p) (singleton_mem (velocity c p))
  let M : ℝ := max |(J.lo:ℝ)| |(J.hi:ℝ)|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hdb (w : ℝ) (hw : w ∈ Set.Icc (floor.lo:ℝ) (floor.hi:ℝ)) : ‖deriv f w‖ ≤ M := by
    rw [(hd w).deriv,Real.norm_eq_abs,abs_le]
    have hj := hJ w hw
    exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hj.1),
      hj.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have hL := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (C := M)
    (fun w _ => (hd w).differentiableAt) hdb (convex_Icc _ _) (middle_mem hf) hh
  have hm : |h-(middle floor:ℝ)| ≤ ((floor.hi:ℝ)-floor.lo)/2 := by
    unfold middle
    push_cast
    exact abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at hL
  refine hL.trans ((mul_le_mul_of_nonneg_left hm hM).trans_eq ?_)
  simp [floorError,M,J]

/-- Accumulate the sample errors with the absolute values of the signed pair coefficients. -/
theorem centerApprox_sound {F : ℕ → ℝ → ℝ} {sample : ℚ → ℚ} {eps : ℚ} {ok : ℚ → Bool}
    {floor : Interval} {c : Center}
    (hsamp : ∀ d : ℚ, d ∈ Set.Icc 0 1 → ok d = true →
      |F 0 (d:ℝ) - (sample d:ℝ)| ≤ (eps:ℝ))
    (hf : fitFloor floor = true) (hc : simplex (liftCenter c))
    (hok : accurateCenter ok floor c = true) :
    |expression .value F (middle floor) (liftCenter c) - (centerApprox sample floor c : ℝ)| ≤
      (pairs.card : ℝ) * (eps:ℝ) := by
  let d (p : Pair) := distQ (middle floor) c p
  let e (p : Pair) : ℝ := (coefficient p:ℝ) * (F 0 (d p:ℝ) - sample (d p))
  have hr (p : Pair) (hp : p ∈ pairs) : |e p| ≤ (eps:ℝ) := by
    have hmid := middle_mem hf
    have hdata := floor_data hf
    have hdist := distance_unit (hdata.1.trans hmid.1) (hmid.2.trans hdata.2.2) hc p
    rw [← cast_distQ] at hdist
    have hdom : d p ∈ Set.Icc 0 1 := ⟨by exact_mod_cast hdist.1,by exact_mod_cast hdist.2⟩
    have h := hsamp (d p) hdom ((of_decide_eq_true hok) p hp)
    simpa [e, coefficient, abs_mul, abs_pow] using h
  have he : expression .value F (middle floor) (liftCenter c) - (centerApprox sample floor c : ℝ)
      = ∑ p ∈ pairs, e p := by
    rw [value_eq_sum]
    unfold centerApprox
    push_cast
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun p _ => by simp [e,d,cast_distQ,mul_sub])
  rw [he]
  exact (abs_sum_le_sum_abs e pairs).trans ((sum_le_sum hr).trans_eq (by simp))

/-- Full radius used by both sides of the strict trial comparison. -/
theorem centerRadius_sound {F : ℕ → ℝ → ℝ} {q : Oracle} {sample : ℚ → ℚ} {eps : ℚ}
    {ok : ℚ → Bool} {floor : Interval} {B : Box 6} {c : Center} {h : ℝ}
    (hF : ∀ x, HasDerivAt (F 0) (F 1 x) x) (hq : FirstOracleSound q F)
    (hsamp : ∀ d : ℚ, d ∈ Set.Icc 0 1 → ok d = true →
      |F 0 (d:ℝ) - (sample d:ℝ)| ≤ (eps:ℝ))
    (hf : fitFloor floor = true) (hb : B.Mem (liftCenter c)) (hc : simplex (liftCenter c))
    (hok : accurateCenter ok floor c = true) (hh : floor.Mem h) :
    |expression .value F h (liftCenter c) - (centerApprox sample floor c:ℝ)| ≤
      (centerRadius q eps floor B c:ℝ) := by
  refine (abs_sub_le _ (expression .value F (middle floor) (liftCenter c)) _).trans ?_
  have h := add_le_add (floorError_sound hF hq hf hb hc hh) (centerApprox_sound hsamp hf hc hok)
  exact h.trans_eq (by simp [centerRadius,add_comm])

#print axioms centerRadius_sound

end GaussianChains.Band



