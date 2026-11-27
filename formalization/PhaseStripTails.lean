import PackedFaceSlopesBounds

/-! Rigorous truncation radii used for the six positive modes in the strip
root and phase-width certificates. All radii concern real infinite sums. -/
noncomputable section
namespace GaussianChains.PackedFace
open Finset Set

/-- Geometric tail starting at frequency 7. The leading term keeps the
actual nome; only the common ratio uses the uniform bound 17/50. -/
def sixTail (q : ℝ) (p : ℕ) : ℝ :=
  weightedMode q p 7 / (1 - tailRatio faceQ p 7)

private theorem six_ratio_lt_one {p : ℕ} (hp : p = 2 ∨ p = 4) :
    tailRatio faceQ p 7 < 1 := by
  rcases hp with rfl | rfl <;> norm_num [tailRatio, faceQ]

/-- Any sequence dominated from the seventh mode on has a controlled
difference between its positive-frequency sum and its first six entries. -/
theorem six_mode_remainder {q C : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hC : 0 ≤ C) {p : ℕ} (hp : p = 2 ∨ p = 4) (f : ℕ → ℝ)
    (h : ∀ k : ℕ, |f (k+7)| ≤ C * weightedMode q p (k+7)) :
    Summable (fun k : ℕ => f (k+1)) ∧
      |(∑' k : ℕ, f (k+1)) - ∑ k ∈ range 6, f (k+1)| ≤ C * sixTail q p := by
  have ⟨hw,hw'⟩ := weightedMode_tail hq hQ (by norm_num [faceQ])
    p 7 (by decide) (six_ratio_lt_one hp)
  have hh (k : ℕ) : ‖f (k+7)‖ ≤ C*weightedMode q p (k+7) := by
    simpa only [Real.norm_eq_abs] using h k
  have hm := hw.hasSum.mul_left C
  have htail : Summable (fun k : ℕ => f (k+7)) := Summable.of_norm_bounded hm.summable hh
  have hs : Summable (fun k : ℕ => f (k+1)) :=
    (summable_nat_add_iff 6).mp (by simpa only [Nat.add_assoc] using htail)
  refine ⟨hs, ?_⟩
  have hsplit := hs.sum_add_tsum_nat_add 6
  change (∑ k ∈ range 6, f (k+1)) + (∑' k : ℕ, f (k+7)) = _ at hsplit
  rw [← hsplit, add_sub_cancel_left]
  have hb := tsum_of_norm_bounded hm hh
  rw [Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hw' hC)

private theorem sixTail_mono {q : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    {p : ℕ} (hp : p = 2 ∨ p = 4) : sixTail q p ≤ sixTail faceQ p := by
  unfold sixTail weightedMode
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hq hQ _) (by positivity)) (sub_nonneg.mpr (six_ratio_lt_one hp).le)

theorem slope_six_bound {q x z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) :
    |endpointSlope q x z - ∑ k ∈ range 6, endpointMode (k+1) q x z| ≤ 9*sixTail q 2 :=
  (six_mode_remainder hq hQ (by norm_num : (0:ℝ) ≤ 9) (.inl rfl)
    (fun n => endpointMode n q x z) (fun k => endpointMode_bound _ hq hx hz)).2

theorem dx_six_bound {q x z dz : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) (hd : |dz| ≤ 3) :
    |(∑' k : ℕ, endpointDx (k+1) q x z dz) -
      ∑ k ∈ range 6, endpointDx (k+1) q x z dz| ≤ 39*sixTail q 4 :=
  (six_mode_remainder hq hQ (by norm_num : (0:ℝ) ≤ 39) (.inr rfl)
    (fun n => endpointDx n q x z dz) (fun k => endpointDx_bound (by omega) hq hx hz hd)).2

theorem scaled_dq_six_bound {q x z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) :
    |q*(∑' k : ℕ, endpointDq (k+1) q x z) -
      ∑ k ∈ range 6, q*endpointDq (k+1) q x z| ≤ 9*sixTail q 4 := by
  rw [← tsum_mul_left]
  exact (six_mode_remainder hq hQ (by norm_num : (0:ℝ) ≤ 9) (.inr rfl)
    (fun n => q*endpointDq n q x z)
    (fun k => endpointDq_scaled_bound (by omega) hq hx hz)).2

/-- Uniform exact rational bounds. All integer power evaluations in these
three endpoints are checked by norm_num in the Lean kernel. -/
theorem slope_six_error {q x z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) :
    |endpointSlope q x z - ∑ k ∈ range 6, endpointMode (k+1) q x z| < 2/10^20 :=
  (slope_six_bound hq hQ hx hz).trans_lt ((mul_le_mul_of_nonneg_left
    (sixTail_mono hq hQ (.inl rfl)) (by norm_num : (0:ℝ) ≤ 9)).trans_lt
      (by norm_num [sixTail, weightedMode, tailRatio, faceQ]))

theorem dx_six_error {q x z dz : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) (hd : |dz| ≤ 3) :
    |(∑' k : ℕ, endpointDx (k+1) q x z dz) -
      ∑ k ∈ range 6, endpointDx (k+1) q x z dz| < 4/10^18 :=
  (dx_six_bound hq hQ hx hz hd).trans_lt ((mul_le_mul_of_nonneg_left
    (sixTail_mono hq hQ (.inr rfl)) (by norm_num : (0:ℝ) ≤ 39)).trans_lt
      (by norm_num [sixTail, weightedMode, tailRatio, faceQ]))

theorem scaled_dq_six_error {q x z : ℝ} (hq : 0 ≤ q) (hQ : q ≤ faceQ)
    (hx : x ∈ Set.Icc (-1) 1) (hz : z ∈ Set.Icc (-1) 1) :
    |q*(∑' k : ℕ, endpointDq (k+1) q x z) -
      ∑ k ∈ range 6, q*endpointDq (k+1) q x z| < 8/10^19 :=
  (scaled_dq_six_bound hq hQ hx hz).trans_lt ((mul_le_mul_of_nonneg_left
    (sixTail_mono hq hQ (.inr rfl)) (by norm_num : (0:ℝ) ≤ 9)).trans_lt
      (by norm_num [sixTail, weightedMode, tailRatio, faceQ]))

end GaussianChains.PackedFace

