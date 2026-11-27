import ClusterSeriesParity
import Mathlib.Analysis.Asymptotics.Defs

namespace GaussianChains.ClusterSeries

open scoped Asymptotics

/-- Absolute, uniform-in-angular-gap estimate after summation. The constant
depends on the two fixed block sizes and the nome. -/
theorem packedMass_fourth_bound (k l : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, |packedMass k l q η - massPoly k l q η| ≤ K * η^6 := by
  obtain ⟨C, hC, hpoint⟩ := block_square_fourth_bound k l
  let moment : ℝ := ∑' n : ℕ, q^((n+1)^2) * ((n+1:ℕ):ℝ)^6
  have hm : 0 ≤ moment := tsum_nonneg (fun n => by positivity)
  refine ⟨C * moment, mul_nonneg hC hm, ?_⟩
  intro η
  let e (n : ℕ) : ℝ := (-1:ℝ)^(n+1)
  let u (n : ℕ) : ℝ := ((n+1:ℕ):ℝ) * η
  let r (n : ℕ) : ℝ :=
    (block k (u n) - e n * block l (u n))^2 - modeQuartic k l (e n) (u n)
  have hterm (n : ℕ) : |r n| ≤ C * η^6 * ((n+1:ℕ):ℝ)^6 := by
    calc
      |r n| ≤ C * (u n)^6 := hpoint (e n) (neg_one_pow_eq_or ℝ (n+1)).symm (u n)
      _ = _ := by dsimp only [u]; ring
  obtain ⟨hr, hsum⟩ := gaussian_tsum_remainder_bound hq hq1 6 (C * η^6) r hterm
  have hpoly := modeQuartic_hasSum k l hq hq1 η
  have hmass : HasSum (fun n : ℕ => q^((n+1)^2) * (block k (u n) - e n * block l (u n))^2)
      (massPoly k l q η + ∑' n : ℕ, q^((n+1)^2) * r n) := by
    apply (hpoly.add hr.hasSum).congr_fun
    intro n
    dsimp only [r, u, e]
    ring
  calc
    |packedMass k l q η - massPoly k l q η|
        = |∑' n : ℕ, q^((n+1)^2) * r n| := by
          unfold packedMass
          rw [show (∑' n : ℕ, q^((n+1)^2) * (block k (u n) - e n * block l (u n))^2) =
            massPoly k l q η + ∑' n : ℕ, q^((n+1)^2) * r n from hmass.tsum_eq]
          simp
    _ ≤ C * η^6 * moment := hsum
    _ = _ := by ring

/-- Fourth-order expansion of the packed antipodal energy as a function of
the angular spacing η = 2πh. The polynomial in `massPoly` separates positive
odd and even modes. -/
theorem packedEnergy_fourth (k l : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (c : ℝ) (N : ℕ) :
    (fun η : ℝ => (1 - (2*c/N) * packedMass k l q η) -
      (1 - (2*c/N) * massPoly k l q η)) =O[nhds 0] (fun η : ℝ => η^6) := by
  obtain ⟨K, _, hK⟩ := packedMass_fourth_bound k l hq hq1
  apply Asymptotics.IsBigO.of_bound (|-(2*c/N)| * K)
  apply Filter.Eventually.of_forall
  intro η
  simp only [Real.norm_eq_abs]
  rw [show (1 - (2*c/N) * packedMass k l q η) - (1 - (2*c/N) * massPoly k l q η) =
      -(2*c/N) * (packedMass k l q η - massPoly k l q η) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ η^6), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK η) (abs_nonneg _)

end GaussianChains.ClusterSeries

