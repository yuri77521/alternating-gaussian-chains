import ClusterSeriesSquare
import ClusterSeriesMoment

namespace GaussianChains.ClusterSeries

/-- Gaussian frequencies of the given parity, numbered starting at one. -/
noncomputable def parityTerm (p : ℕ → Prop) [DecidablePred p] (q : ℝ) (d n : ℕ) : ℝ :=
  if p (n + 1) then q ^ ((n + 1) ^ 2) * ((n + 1 : ℕ) : ℝ) ^ d else 0

noncomputable def parityMoment (p : ℕ → Prop) [DecidablePred p] (q : ℝ) (d : ℕ) : ℝ :=
  ∑' n, parityTerm p q d n

theorem parityMoment_hasSum (p : ℕ → Prop) [DecidablePred p]
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (d : ℕ) :
    HasSum (parityTerm p q d) (parityMoment p q d) := by
  apply Summable.hasSum
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (gaussianMoment_summable q hq hq1 d)
  · unfold parityTerm
    split <;> positivity
  · unfold parityTerm
    split
    · exact le_rfl
    · positivity

/-- Constant, quadratic and quartic terms in the positive-frequency mass of
two packed antipodal clusters. The even quartic term survives unequal sizes. -/
noncomputable def massPoly (k l : ℕ) (q η : ℝ) : ℝ :=
  let A := coeff k
  let B := coeff l
  4 * parityMoment Odd q 0
    - (2 * (A+B) * η^2) * parityMoment Odd q 2
    + (((A+B)^2/4 + (A*(A-1)+B*(B-1))/6) * η^4) * parityMoment Odd q 4
    + ((A-B)^2/4 * η^4) * parityMoment Even q 4

theorem modeQuartic_hasSum (k l : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (η : ℝ) :
    HasSum (fun n : ℕ => q ^ ((n + 1)^2) *
      modeQuartic k l ((-1 : ℝ)^(n + 1)) (((n + 1 : ℕ) : ℝ) * η)) (massPoly k l q η) := by
  let A := coeff k
  let B := coeff l
  have h₀ := (parityMoment_hasSum Odd hq hq1 0).mul_left (4 : ℝ)
  have h₂ := (parityMoment_hasSum Odd hq hq1 2).mul_left (2*(A+B)*η^2)
  have h₄o := (parityMoment_hasSum Odd hq hq1 4).mul_left
    (((A+B)^2/4 + (A*(A-1)+B*(B-1))/6)*η^4)
  have h₄e := (parityMoment_hasSum Even hq hq1 4).mul_left ((A-B)^2/4*η^4)
  convert (((h₀.sub h₂).add h₄o).add h₄e) using 1
  ext n
  rcases Nat.even_or_odd (n+1) with h | h
  · simp only [parityTerm, h, if_true, if_false, (Nat.not_odd_iff_even.mpr h),
      h.neg_one_pow, modeQuartic, A, B]
    ring
  · simp only [parityTerm, h, if_true, if_false, (Nat.not_even_iff_odd.mpr h),
      h.neg_one_pow, modeQuartic, A, B]
    ring

/-- The six-site specialization after the per-particle factor is applied. -/
theorem tripleEnergyPoly_eq (q η c : ℝ) :
    1 - (2*c/6) * massPoly 1 1 q η =
      (1 - (4*c/3) * parityMoment Odd q 0)
        + (8*c/3) * parityMoment Odd q 2 * η^2
        - (14*c/9) * parityMoment Odd q 4 * η^4 := by
  simp only [massPoly, coeff, Nat.cast_one]
  ring

end GaussianChains.ClusterSeries
