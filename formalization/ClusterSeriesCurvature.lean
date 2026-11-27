import ClusterSeriesParity
import ClustersWidthKernel

namespace GaussianChains.ClusterSeries

/-- Evaluating the normalized angular cosine series at zero and π selects all
positive odd harmonics, with the first harmonic restored explicitly. -/
theorem angularCos_oddMoment (p : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    q*(angularCos p q 0 - angularCos p q Real.pi) = 2 * parityMoment Odd q p := by
  let W (k : ℕ) := angularWeight p q k
  let V (k : ℕ) := W k * (-1:ℝ)^(k+2)
  have hw : Summable W := summable_widthMoment p hq.le hq1
  have hv : Summable V := hw.of_norm_bounded <| by
    intro k
    have h : 0 ≤ W k := by dsimp [W, angularWeight]; positivity
    simp [V, Real.norm_eq_abs, abs_of_nonneg h]
  have hsum := (parityMoment_hasSum Odd hq hq1 p).summable.tsum_eq_zero_add
  have hz : parityTerm Odd q p 0 = q := by simp [parityTerm]
  have htail (k : ℕ) : q*(W k - V k) = 2 * parityTerm Odd q p (k+1) := by
    have hp : q^((k+2)^2-1)*q = q^((k+2)^2) := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ (k+2)^2 from Nat.one_le_pow _ _ (by omega))]
    rcases Nat.even_or_odd (k+2) with h | h
    · simp [parityTerm, show k+1+1 = k+2 by omega, Nat.not_odd_iff_even.mpr h,
        V, h.neg_one_pow]
    · simp only [parityTerm, show k+1+1 = k+2 by omega, h, if_true, V, h.neg_one_pow,
        W, angularWeight]
      rw [← hp]; ring
  have hd : q*((∑' k, W k) - ∑' k, V k) = 2*(∑' k, parityTerm Odd q p (k+1)) := by
    rw [← hw.tsum_sub hv, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr htail
  have hzero : angularCos p q 0 = 1 + ∑' k, W k := by simp [angularCos, W]
  have hpi : angularCos p q Real.pi = -1 + ∑' k, V k := by
    simp only [angularCos, V, W, Real.cos_pi, Real.cos_nat_mul_pi]
  change (∑' k, parityTerm Odd q p k) = _ at hsum
  rw [hz] at hsum
  rw [hzero, hpi, parityMoment, hsum]
  linarith only [hd]

end GaussianChains.ClusterSeries

