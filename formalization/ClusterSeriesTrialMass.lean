import ClusterSeriesParity
import ClusterSeriesTrial

namespace GaussianChains.ClusterSeries

/-- Fourier-mass deficit of the packed antipodal trial relative to the
collision dipole. Dividing by q gives the normalized D bound of Theorem 1. -/
theorem packedMass_trial_deficit_le (k l : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (η : ℝ) : 4 * parityMoment Odd q 0 - packedMass k l q η ≤
      (2*(coeff k+coeff l)*η^2) * parityMoment Odd q 2 := by
  let z (n : ℕ) : ℝ := ((n+1:ℕ):ℝ)*η
  let p (n : ℕ) : ℝ := block k (z n) - (-1:ℝ)^(n+1)*block l (z n)
  let M : ℝ := (2*(k:ℝ)+1) + (2*(l:ℝ)+1)
  have hp (n : ℕ) : |p n| ≤ M := by
    refine (abs_sub _ _).trans ?_
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact add_le_add (block_abs_le k (z n)) (block_abs_le l (z n))
  have hm : Summable (fun n : ℕ => q^((n+1)^2)*(p n)^2) := by
    apply (gaussian_tsum_remainder_bound hq hq1 0 (M^2) (fun n => (p n)^2) ?_).1
    intro n
    dsimp only
    rw [pow_zero, mul_one, abs_of_nonneg (sq_nonneg _), ← sq_abs (p n)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hp n) _
  have h0 := (parityMoment_hasSum Odd hq hq1 0).mul_left (4 : ℝ)
  have h2 := (parityMoment_hasSum Odd hq hq1 2).mul_left (2*(coeff k+coeff l)*η^2)
  have hterm (n : ℕ) :
      (4 * parityTerm Odd q 0 n - (2*(coeff k+coeff l)*η^2)*parityTerm Odd q 2 n)
      ≤ q^((n+1)^2)*(p n)^2 := by
    rcases Nat.even_or_odd (n+1) with he | ho
    · simp only [parityTerm, if_neg (Nat.not_odd_iff_even.mpr he), mul_zero, sub_zero]
      positivity
    · simp only [parityTerm, if_pos ho, pow_zero, mul_one, p, ho.neg_one_pow,
        neg_one_mul, sub_neg_eq_add]
      have h := trial_odd_deficit_le k l (z n)
      have ht : 4 - 2*(coeff k+coeff l)*η^2*((n+1:ℕ):ℝ)^2 ≤
          (block k (z n) + block l (z n))^2 := by
        dsimp only [z] at h ⊢
        linarith only [h]
      calc
        _ = q^((n+1)^2)*(4-2*(coeff k+coeff l)*η^2*((n+1:ℕ):ℝ)^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ht (pow_nonneg hq.le _)
  have hl := h0.sub h2
  have H := hl.summable.tsum_le_tsum hterm hm
  rw [hl.tsum_eq] at H
  change 4 * parityMoment Odd q 0 - 2*(coeff k+coeff l)*η^2*parityMoment Odd q 2
    ≤ packedMass k l q η at H
  linarith

end GaussianChains.ClusterSeries

