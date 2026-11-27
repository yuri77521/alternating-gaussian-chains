import ChainEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace GaussianChains

noncomputable section

/-- Absolute summability on the full label-pair × period product, without
grouping positive and negative charges first. -/
theorem summable_abs_directed_images {N : ℕ} (α L : ℝ) (hα : 0 < α) (hL : 0 < L)
    (X : Fin N → ℝ) :
    Summable (fun p : (Fin N × Fin N) × ℤ =>
      |charge p.1.1 * charge p.1.2 * primedImage α L X p.1.1 p.1.2 p.2|) := by
  let f (p : (Fin N × Fin N) × ℤ) :=
    charge p.1.1 * charge p.1.2 * primedImage α L X p.1.1 p.1.2 p.2
  change Summable fun p => |f p|
  refine (summable_prod_of_nonneg (f := fun p => |f p|) (fun _ => abs_nonneg _)).2
    ⟨?_, (hasSum_fintype _).summable⟩
  rintro ⟨i, j⟩
  change Summable fun k : ℤ => |charge i * charge j * primedImage α L X i j k|
  apply Summable.abs
  exact (primedImage_hasSum α L hα hL X i j).summable.mul_left (charge i * charge j)

theorem kernel_neg (s d : ℝ) : kernel s (-d) = kernel s d := by
  unfold kernel
  conv_rhs => rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 1
  ring

theorem kernel_add_int (s d : ℝ) (t : ℤ) : kernel s (d + (t : ℝ)) = kernel s d := by
  unfold kernel
  conv_rhs => rw [← (Equiv.addRight t).tsum_eq]
  apply tsum_congr
  intro k
  simp only [Equiv.coe_addRight, Int.cast_add]
  congr 1
  ring

/-- The signed unordered pair score used for block translations and contact tests. -/
def pairScore {N : ℕ} (s : ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then charge i * charge j * kernel s (x j - x i) else 0

theorem imageEnergy_eq_pairScore {N : ℕ} (hN : 0 < N) (s : ℝ) (x : Fin N → ℝ) :
    imageEnergy s x = 1 - kernel s 0 - 2 * pairScore s x / (N : ℝ) := by
  classical
  let K (i j : Fin N) := charge i * charge j * kernel s (x j - x i)
  let U (i j : Fin N) := if i < j then K i j else 0
  have sym (i j : Fin N) : K i j = K j i := by
    dsimp [K]
    rw [← neg_sub (x j) (x i), kernel_neg, mul_comm (charge i)]
  have splitPair (i j : Fin N) :
      K i j = U i j + U j i + (if i = j then kernel s 0 else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [U, h, h.ne, h.asymm]
    · simp [U, K, charge_mul_self]
    · simp [U, h, h.ne', h.asymm, sym i j]
  have splitSum : (∑ i, ∑ j, K i j) = 2 * pairScore s x + (N : ℝ) * kernel s 0 := by
    simp_rw [splitPair, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => U j i)]
    simp [two_mul, U, K, pairScore]
  change 1 - (1 / (N : ℝ)) * (∑ i, ∑ j, K i j) = _
  rw [splitSum]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

/-- Maximizing the score and minimizing the physical energy give the same
order on configurations at a fixed width and label count. -/
theorem imageEnergy_le_iff_pairScore_ge {N : ℕ} (hN : 0 < N) (s : ℝ)
    (x y : Fin N → ℝ) : imageEnergy s x ≤ imageEnergy s y ↔ pairScore s y ≤ pairScore s x := by
  rw [imageEnergy_eq_pairScore hN, imageEnergy_eq_pairScore hN, sub_le_sub_iff_left,
    div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hN), mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<2)]

theorem imageEnergy_lt_iff_pairScore_gt {N : ℕ} (hN : 0 < N) (s : ℝ)
    (x y : Fin N → ℝ) : imageEnergy s x < imageEnergy s y ↔ pairScore s y < pairScore s x := by
  rw [← not_le, imageEnergy_le_iff_pairScore_ge hN, not_le]

end

end GaussianChains
