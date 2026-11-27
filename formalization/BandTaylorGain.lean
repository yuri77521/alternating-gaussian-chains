import BandTaylorBase

/-! The score increase from the feasible center to any point of a closed slack box. -/
namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Strip Interval Finset

theorem sum_over_cuts (f : Pair → ℝ) (d : Fin 6 → ℝ) :
    ∑ p ∈ pairs, f p * (∑ k ∈ arc p.1 p.2, d k) =
      ∑ k, d k * (∑ p ∈ pairs.filter (fun p => k ∈ arc p.1 p.2), f p) := by
  classical
  calc
    _ = ∑ p ∈ pairs, ∑ k, if k ∈ arc p.1 p.2 then f p*d k else 0 := by
      apply sum_congr rfl
      intro p hp
      rw [mul_sum, ← sum_filter]
      simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro p _
      by_cases h : k ∈ arc p.1 p.2 <;> simp [h, mul_comm]

def seg (c u : Fin 6 → ℝ) (t : ℝ) (i : Fin 6) := mix (c i) (u i) t

private theorem distance_segment (h : ℝ) (c u : Fin 6 → ℝ) (t : ℝ) (p : Pair) :
    distance h (seg c u t) p = distance h c p +
      t*((1-6*h)*∑ k ∈ arc p.1 p.2, (u k-c k)) := by
  simp [distance, seg, mix, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  ring

def cutGradient (F : ℕ → ℝ → ℝ) (h : ℝ) (u : Fin 6 → ℝ) (k : Fin 6) : ℝ :=
  ∑ p ∈ pairs.filter (fun p => k ∈ arc p.1 p.2), (coefficient p:ℝ)*F 1 (distance h u p)

theorem cutBounds_sound {F : ℕ → ℝ → ℝ} {q : Oracle} (hq : FirstOracleSound q F)
    {floor : Interval} {B : Box 6} {h : ℝ} {u : Fin 6 → ℝ} (hf : fitFloor floor = true)
    (hh : floor.Mem h) (hb : B.Mem u) (hs : simplex u) (k : Fin 6) :
    (cutBounds q floor B k).Mem (cutGradient F h u k) :=
  sumRange_mem fun p _ => pairSlope_sound hq hf hh hb hs p

theorem score_segment_deriv {F : ℕ → ℝ → ℝ} (hF : ∀ x, HasDerivAt (F 0) (F 1 x) x)
    (h : ℝ) (c u : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt (fun w => expression .value F h (seg c u w))
      ((1-6*h)* ∑ k, (u k-c k) * cutGradient F h (seg c u t) k) t := by
  let D (p : Pair) := (1-6*h)*∑ k ∈ arc p.1 p.2, (u k-c k)
  have hd (p : Pair) (_hp : p ∈ pairs) :
      HasDerivAt (fun w => distance h (seg c u w) p) (D p) t := by
    simp_rw [distance_segment]
    simpa [D] using ((hasDerivAt_id t).mul_const (D p)).const_add (distance h c p)
  simp_rw [value_eq_sum]
  refine (sum_deriv hF hd).congr_deriv ?_
  unfold cutGradient
  rw [← sum_over_cuts (fun p => (coefficient p:ℝ)*F 1 (distance h (seg c u t) p)) (fun k => u k-c k)]
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  dsimp [D]
  ring

/-- Sharp signed product bound used in the frozen implementation. The extrema
with equal signs are the only candidates for a positive gain. -/
theorem delta_mul_le {g d c l u a b : ℝ}
    (hd : l ≤ d ∧ d ≤ u) (hc : l ≤ c ∧ c ≤ u) (hg : a ≤ g ∧ g ≤ b) :
    (d-c)*g ≤ max (max ((u-c)*b) ((l-c)*a)) 0 := by
  rcases le_total 0 g with hg0 | hg0
  · rcases le_total c d with h | h
    · exact (mul_le_mul (sub_le_sub_right hd.2 c) hg.2 hg0 (sub_nonneg.mpr hc.2)).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hg0).trans (le_max_right _ _)
  · rcases le_total d c with h | h
    · have hh : (c-d)*(-g) ≤ (c-l)*(-a) :=
        mul_le_mul (sub_le_sub_left hd.1 c) (neg_le_neg hg.1) (neg_nonneg.mpr hg0) (sub_nonneg.mpr hc.1)
      have hdg : (d-c)*g ≤ (l-c)*a := by linarith only [hh]
      exact hdg.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h) hg0).trans (le_max_right _ _)

theorem shiftGain_sound {F : ℕ → ℝ → ℝ} {q : Oracle} {floor : Interval} {B : Box 6}
    {h : ℝ} {u : Fin 6 → ℝ} {c : Center}
    (hF : ∀ x, HasDerivAt (F 0) (F 1 x) x) (hq : FirstOracleSound q F)
    (hf : fitFloor floor = true) (hh : floor.Mem h) (hu : B.Mem u) (hs : simplex u)
    (hc : B.Mem (liftCenter c)) (hsc : simplex (liftCenter c)) :
    expression .value F h u - expression .value F h (liftCenter c) ≤
      (shiftGain q floor B c : ℝ) := by
  obtain ⟨t,ht,he⟩ := unit_mvt (score_segment_deriv hF h (liftCenter c) u)
  have h1 : seg (liftCenter c) u 1 = u := by ext i; simp [seg, mix]
  have h0 : seg (liftCenter c) u 0 = liftCenter c := by ext i; simp [seg, mix]
  rw [h1,h0] at he
  rw [he]
  let w := seg (liftCenter c) u t
  have hw : B.Mem w := fun i => mix_mem (hc i) (hu i) (Set.Ioo_subset_Icc_self ht)
  have hsw : simplex w := mixed_simplex hsc hs (Set.Ioo_subset_Icc_self ht)
  let G (k : Fin 6) : ℝ :=
    max (max ((((B k).hi:ℝ)-(c k:ℝ))*(cutBounds q floor B k).hi)
             ((((B k).lo:ℝ)-(c k:ℝ))*(cutBounds q floor B k).lo)) 0
  have hG (k : Fin 6) : (u k-liftCenter c k)*cutGradient F h w k ≤ G k :=
    delta_mul_le (hu k) (hc k) (cutBounds_sound hq hf hh hw hsw k)
  have hS : 0 ≤ 1-6*h := by linarith [(hh.2.trans (floor_data hf).2.2)]
  have hS' : 1-6*h ≤ 1-6*(floor.lo:ℝ) := by linarith [hh.1]
  calc
    _ ≤ (1-6*h) * ∑ k, G k := mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => hG k) hS
    _ ≤ (1-6*(floor.lo:ℝ)) * ∑ k, G k :=
      mul_le_mul_of_nonneg_right hS' (sum_nonneg fun k _ => le_max_right _ _)
    _ = _ := by simp [shiftGain, G]

end GaussianChains.Band

