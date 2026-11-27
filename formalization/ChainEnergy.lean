import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The signed, directed Gaussian energy per label. The prime on the physical
image sum removes exactly the pair of equal labels in the central period.
Distinct labels at a coincident site still interact. -/

noncomputable section

namespace GaussianChains

/-- Label zero has positive charge. -/
def charge {N : ℕ} (i : Fin N) : ℝ := (-1 : ℝ) ^ i.val

theorem charge_mul_self {N : ℕ} (i : Fin N) : charge i * charge i = 1 := by
  simp [charge, ← mul_pow]

/-- Periodized Gaussian with unit period and dimensionless width parameter. -/
def kernel (s d : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-s * (d + (k : ℝ)) ^ 2)

theorem kernel_hasSum (s d : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℤ => Real.exp (-s * (d + (k : ℝ)) ^ 2))
      (HurwitzZeta.evenKernel (d : ℝ) (s / Real.pi)) := by
  apply (HurwitzZeta.hasSum_int_evenKernel d (show 0 < s / Real.pi by positivity)).congr_fun
  intro k
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

theorem kernel_summable (s d : ℝ) (hs : 0 < s) :
    Summable (fun k : ℤ => Real.exp (-s * (d + (k : ℝ)) ^ 2)) :=
  (kernel_hasSum s d hs).summable

/-- Eq. (2), in which the kernel includes every image, including the central one. -/
def imageEnergy {N : ℕ} (s : ℝ) (x : Fin N → ℝ) : ℝ :=
  1 - (1 / (N : ℝ)) * ∑ i, ∑ j, charge i * charge j * kernel s (x j - x i)

/-- Literal primed image series, with displacements in physical units. -/
def primedImage {N : ℕ} (α L : ℝ) (X : Fin N → ℝ) (i j : Fin N) (k : ℤ) : ℝ :=
  if i = j ∧ k = 0 then 0 else Real.exp (-α * (X j - X i + L * (k : ℝ)) ^ 2)

/-- Ordered energy per particle for arbitrary label positions in one physical period. -/
def physicalEnergy {N : ℕ} (α L : ℝ) (X : Fin N → ℝ) : ℝ :=
  -(∑ i, ∑ j, charge i * charge j * (∑' k : ℤ, primedImage α L X i j k)) / (N : ℝ)

/-- Physical and unit-period image series agree term by term when scaled. -/
theorem scaled_image (α L u v : ℝ) (hL : L ≠ 0) (k : ℤ) :
    Real.exp (-α * (v - u + L * (k : ℝ)) ^ 2) =
      Real.exp (-(α * L ^ 2) * ((v / L - u / L) + (k : ℝ)) ^ 2) := by
  congr 1
  field_simp

theorem physical_images_hasSum (α L u v : ℝ) (hα : 0 < α) (hL : 0 < L) :
    HasSum (fun k : ℤ => Real.exp (-α * (v - u + L * (k : ℝ)) ^ 2))
      (kernel (α * L ^ 2) (v / L - u / L)) := by
  simp_rw [scaled_image α L u v hL.ne']
  exact (kernel_summable (α * L ^ 2) _ (by positivity)).hasSum

/-- Removing the central self interaction changes each diagonal pair sum by one,
including on the collision closure where distinct labels may have the same position. -/
theorem primedImage_hasSum {N : ℕ} (α L : ℝ) (hα : 0 < α) (hL : 0 < L)
    (X : Fin N → ℝ) (i j : Fin N) :
    HasSum (primedImage α L X i j)
      (kernel (α * L ^ 2) (X j / L - X i / L) - if i = j then 1 else 0) := by
  have h := physical_images_hasSum α L (X i) (X j) hα hL
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    apply (h.sub (hasSum_ite_eq (0 : ℤ) (1 : ℝ))).congr_fun
    intro k
    by_cases hk : k = 0 <;> simp [primedImage, hk]
  · rw [if_neg hij, sub_zero]
    exact h.congr_fun (fun k => by simp [primedImage, hij])

/-- Summation over all directed pairs commutes with the sum over physical periods. -/
theorem ordered_images_hasSum {N : ℕ} (α L : ℝ) (hα : 0 < α) (hL : 0 < L)
    (X : Fin N → ℝ) :
    HasSum (fun k : ℤ => ∑ i, ∑ j, charge i * charge j * primedImage α L X i j k)
      (∑ i, ∑ j, charge i * charge j * ∑' k : ℤ, primedImage α L X i j k) := by
  apply hasSum_sum
  intro i _
  apply hasSum_sum
  intro j _
  exact ((primedImage_hasSum α L hα hL X i j).summable.hasSum).mul_left _

/-- The first energy identity in §2. It holds at all positive widths and periods,
without a separation assumption, and therefore also at a boundary collision. -/
theorem physicalEnergy_eq_imageEnergy {N : ℕ} (hN : 0 < N)
    (α L : ℝ) (hα : 0 < α) (hL : 0 < L) (X : Fin N → ℝ) :
    physicalEnergy α L X = imageEnergy (α * L ^ 2) (fun i => X i / L) := by
  classical
  unfold physicalEnergy imageEnergy
  simp_rw [(primedImage_hasSum α L hα hL X _ _).tsum_eq, mul_sub, Finset.sum_sub_distrib]
  have diag (i : Fin N) : (∑ j : Fin N, charge i * charge j * (if i = j then 1 else 0)) = 1 := by
    simp [mul_ite, charge_mul_self]
  simp_rw [diag]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

end GaussianChains
