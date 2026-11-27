import AlternatingMoments

/-! Signed moments of one odd block, in the local orientation in which its
first charge is positive. The argument uses angular coordinates throughout. -/
noncomputable section

open Finset AlternatingMoments

namespace GaussianChains.OddBlock

/-- The variance polynomial for successive pairs of gaps `a₀,b₀,a₁,b₁,…`. -/
def gapVariance (j : ℕ) (a b : ℕ → ℝ) : ℝ :=
  2 * ∑ r ∈ range j, b r * ∑ i ∈ range (r + 1), a i

/-- Equation (4), including its lower bound for arbitrary odd block size. -/
theorem variance_lower (u : ℕ → ℝ) (j : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hg : ∀ i < 2 * j, η ≤ u (i + 1) - u i) :
    (j : ℝ) * ((j : ℝ) + 1) * η ^ 2 ≤
      altSum (fun i => u i ^ 2) j - (altSum u j) ^ 2 := by
  rw [secondMoment]
  have hprefix (r : ℕ) (hr : r < j) :
      ((r : ℝ) + 1) * η ≤ ∑ i ∈ range (r + 1), gapA u i := by
    calc
      _ = ∑ _i ∈ range (r+1), η := by simp
      _ ≤ _ := sum_le_sum fun i hi => hg (2*i) (by
        have := mem_range.mp hi
        omega)
  have bound (n : ℕ) (hn : n ≤ j) : (n : ℝ) * ((n : ℝ) + 1) * η ^ 2 ≤
      2 * ∑ r ∈ range n, gapB u r * ∑ i ∈ range (r + 1), gapA u i := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn' : n < j := by omega
      have hb : η ≤ gapB u n := hg (2 * n + 1) (by omega)
      have hprod := mul_le_mul hb (hprefix n hn')
        (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hη) (le_trans hη hb)
      have hp := ih (by omega)
      rw [sum_range_succ, Nat.cast_succ]
      nlinarith
  exact bound j le_rfl

/-- In a packed progression the signed first moment is exactly its midpoint;
the lower variance bound is attained. This includes the singleton. -/
theorem packed_moments (j : ℕ) (u₀ η : ℝ) :
    let u := fun i : ℕ => u₀ + i*η
    altSum u j = u₀ + j*η ∧
    altSum (fun i => u i^2) j - (altSum u j)^2 = (j:ℝ)*(j+1)*η^2 := by
  let u := fun i : ℕ => u₀ + i*η
  have ha (r : ℕ) : gapA u r = η := by unfold gapA u; push_cast; ring
  have hb (r : ℕ) : gapB u r = η := by unfold gapB u; push_cast; ring
  change altSum u j = _ ∧ altSum (fun i => u i ^ 2) j - (altSum u j)^2 = _
  constructor
  · rw [firstMoment]
    simp [hb, u]
  · rw [secondMoment]
    simp_rw [ha, hb]
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ, mul_add, ih, Nat.cast_succ]; ring

/-- For fixed gaps `b`, increasing gap `a p` by `t` increases the variance
linearly, with a coefficient that counts every `b r` weakly to its right. -/
theorem varyA (j p : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    gapVariance j (fun i => a i + if i = p then t else 0) b =
      gapVariance j a b + (2 * ∑ r ∈ range j, if p ≤ r then b r else 0) * t := by
  unfold gapVariance
  simp_rw [sum_add_distrib, sum_ite_eq', mem_range, Nat.lt_succ_iff,
    mul_add, sum_add_distrib]
  rw [mul_add, mul_assoc, sum_mul]
  congr 2
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp

/-- The coefficient for `b p` is twice the sum of the preceding `a` gaps. -/
theorem varyB (j p : ℕ) (hp : p < j) (a b : ℕ → ℝ) (t : ℝ) :
    gapVariance j a (fun r => b r + if r = p then t else 0) =
      gapVariance j a b + (2 * ∑ i ∈ range (p+1), a i) * t := by
  unfold gapVariance
  simp_rw [add_mul, sum_add_distrib, mul_add]
  simp only [ite_mul, zero_mul, sum_ite_eq', mem_range, hp, ↓reduceIte]
  ring

/-- All internal gap derivatives, in the coordinates of equation (4).
The parameter of differentiation is an increment, evaluated at zero. -/
theorem gap_derivatives (j p : ℕ) (hp : p < j) (a b : ℕ → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (ha : ∀ i < j, η ≤ a i) (hb : ∀ i < j, η ≤ b i) :
    let A := 2 * ∑ r ∈ range j, if p ≤ r then b r else 0
    let B := 2 * ∑ i ∈ range (p+1), a i
    HasDerivAt (fun t => gapVariance j (fun i => a i + if i = p then t else 0) b) A 0 ∧
    HasDerivAt (fun t => gapVariance j a (fun r => b r + if r = p then t else 0)) B 0 ∧
    2 * η ≤ A ∧ 2 * η ≤ B := by
  dsimp only
  have hA : b p ≤ ∑ r ∈ range j, if p ≤ r then b r else 0 := by
    calc
      _ = (if p ≤ p then b p else 0) := by simp
      _ ≤ _ := single_le_sum (f := fun r => if p ≤ r then b r else 0)
        (fun r hr => by dsimp only; split_ifs <;> first | exact hη.trans (hb r (mem_range.mp hr)) | rfl)
        (mem_range.mpr hp)
  have hB : a p ≤ ∑ i ∈ range (p+1), a i := single_le_sum
    (fun i hi => hη.trans (ha i (by have := mem_range.mp hi; omega)))
    (mem_range.mpr (Nat.lt_succ_self p))
  refine ⟨?_, ?_, by linarith [hb p hp], by linarith [ha p hp]⟩
  · simp_rw [varyA]
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul
      (2 * ∑ r ∈ range j, if p ≤ r then b r else 0)).const_add (gapVariance j a b))
  · simp_rw [varyB j p hp]
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul
      (2 * ∑ i ∈ range (p+1), a i)).const_add (gapVariance j a b))

end GaussianChains.OddBlock
