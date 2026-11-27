import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The moving part of the antipodal locking functional is the signed
ordered interaction of the two packed odd progressions. -/
noncomputable section

namespace GaussianChains.Clusters
open Finset

def packedSign {k : ℕ} (i : Fin (2*k+1)) : ℝ := (-1 : ℝ)^i.val
def packedOffset {k : ℕ} (η : ℝ) (i : Fin (2*k+1)) : ℝ := (i.val - (k : ℝ))*η

@[simp] theorem packedOffset_rev {k : ℕ} (η : ℝ) (i : Fin (2*k+1)) :
    packedOffset η i.rev = -packedOffset η i := by
  have hr : (i.rev.val : ℝ) + (i.val : ℝ) = 2*(k : ℝ) := by exact_mod_cast i.rev_add_cast
  unfold packedOffset
  linear_combination η * hr

@[simp] theorem packedSign_rev {k : ℕ} (i : Fin (2*k+1)) : packedSign i.rev = packedSign i := by
  have hr : packedSign i.rev * packedSign i = 1 := by
    rw [packedSign, packedSign, ← pow_add, i.rev_add_cast, pow_mul]
    norm_num
  have hsq : packedSign i * packedSign i = 1 := by
    rw [packedSign, ← mul_pow]
    norm_num
  calc
    packedSign i.rev = packedSign i.rev * (packedSign i * packedSign i) := by rw [hsq, mul_one]
    _ = packedSign i := by rw [← mul_assoc, hr, one_mul]

@[simp] theorem abs_packedSign {k : ℕ} (i : Fin (2*k+1)) : |packedSign i| = 1 := by
  simp [packedSign, abs_pow]

@[simp] theorem sum_packedSign (k : ℕ) : ∑ i : Fin (2*k+1), packedSign i = 1 := by
  simpa [packedSign] using Fin.sum_neg_one_pow ℝ (2*k+1)

/-- The factor of two counts both ordered cross-block interactions. -/
def packedCross (k l : ℕ) (η : ℝ) (K : ℝ → ℝ) (v : ℝ) : ℝ :=
  2 * ∑ i : Fin (2*k+1), ∑ j : Fin (2*l+1), packedSign i * packedSign j *
    K (Real.pi + (v + (packedOffset η i - packedOffset η j)))

theorem packedCross_even (k l : ℕ) (η : ℝ) {K : ℝ → ℝ}
    (hK : ∀ z, K (Real.pi + (-z)) = K (Real.pi + z)) (v : ℝ) :
    packedCross k l η K (-v) = packedCross k l η K v := by
  let f (i : Fin (2*k+1)) (j : Fin (2*l+1)) := packedSign i * packedSign j *
    K (Real.pi + ((-v) + (packedOffset η i - packedOffset η j)))
  have revL : (∑ i : Fin (2*k+1), ∑ j : Fin (2*l+1), f i.rev j.rev) = ∑ i, ∑ j, f i j := by
    calc
      _ = ∑ i : Fin (2*k+1), ∑ j, f i.rev j := by
        apply sum_congr rfl
        intro i _
        exact Equiv.sum_comp Fin.revPerm (f i.rev)
      _ = _ := Equiv.sum_comp Fin.revPerm (fun i => ∑ j, f i j)
  change 2 * (∑ i, ∑ j, f i j) = _
  rw [← revL]
  unfold packedCross
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [f, packedSign_rev, packedOffset_rev]
  rw [show -v + (-packedOffset η i - -packedOffset η j) =
    -(v + (packedOffset η i - packedOffset η j)) by ring, hK]

theorem packedCross_hasDerivAt (k l : ℕ) (η : ℝ) {K D : ℝ → ℝ}
    (hK : ∀ x, HasDerivAt K (D x) x) (v : ℝ) :
    HasDerivAt (packedCross k l η K) (packedCross k l η D v) v := by
  unfold packedCross
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  apply HasDerivAt.const_mul
  simpa using (hK _).comp v (((hasDerivAt_id v).add_const
    (packedOffset η i - packedOffset η j)).const_add Real.pi)

/-- A uniform pointwise second-derivative error adds over the actual
number of signed pairs, even for two unequal odd blocks. -/
theorem packedCross_error (k l : ℕ) (η : ℝ) (K : ℝ → ℝ) (v d ε : ℝ)
    (h : ∀ (i : Fin (2*k+1)) (j : Fin (2*l+1)),
      |K (Real.pi + (v + (packedOffset η i - packedOffset η j))) - d| ≤ ε) :
    |packedCross k l η K v - 2*d| ≤ 2*((2*k+1 : ℕ) : ℝ)*((2*l+1 : ℕ) : ℝ)*ε := by
  let a (i : Fin (2*k+1)) (j : Fin (2*l+1)) := packedSign i * packedSign j
  let e (i : Fin (2*k+1)) (j : Fin (2*l+1)) :=
    a i j * (K (Real.pi + (v + (packedOffset η i - packedOffset η j))) - d)
  have he (i j) : |e i j| ≤ ε := by simpa [e, a, abs_mul] using h i j
  have constSum : ∑ i : Fin (2*k+1), ∑ j : Fin (2*l+1), a i j * d = d := by
    simp [a, ← sum_mul, ← mul_sum]
  have rep : 2*(∑ i, ∑ j, e i j) = packedCross k l η K v - 2*d := by
    simp only [e, mul_sub, sum_sub_distrib, constSum]
    unfold packedCross a
    ring
  rw [← rep, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc
    _ ≤ 2*(∑ i, ∑ j, |e i j|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ 2*(∑ _i : Fin (2*k+1), ∑ _j : Fin (2*l+1), ε) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => sum_le_sum fun j _ => he i j) (by norm_num)
    _ = _ := by simp; ring

/-- Both reflected endpoints of the comparison segment inherit the given
localization, hence so does every intermediate displacement. -/
theorem packed_segment_localized {k l : ℕ} {η v ρ z : ℝ}
    (h : ∀ (i : Fin (2*k+1)) (j : Fin (2*l+1)),
      |v + (packedOffset η i - packedOffset η j)| ≤ ρ)
    (hz : z ∈ Set.Icc (-|v|) |v|) (i : Fin (2*k+1)) (j : Fin (2*l+1)) :
    |z + (packedOffset η i - packedOffset η j)| ≤ ρ := by
  have h₁ := abs_le.mp (h i j)
  have h₂ := abs_le.mp (h i.rev j.rev)
  simp only [packedOffset_rev] at h₂
  rcases abs_cases v with ⟨hv, _⟩ | ⟨hv, _⟩ <;> rw [hv] at hz <;>
    apply abs_le.mpr <;> constructor <;> linarith [h₁.1,h₁.2,h₂.1,h₂.2,hz.1,hz.2]

/-- Localization of each particle in its own antipodal chart supplies the
pairwise bound. The displacement of the midpoints is exactly `a-b`. -/
theorem packed_offsets_localized {k l : ℕ} {a b η R : ℝ}
    (hx : ∀ i : Fin (2*k+1), |a+packedOffset η i| ≤ R)
    (hy : ∀ j : Fin (2*l+1), |b+packedOffset η j| ≤ R)
    (i : Fin (2*k+1)) (j : Fin (2*l+1)) :
    |a-b+(packedOffset η i-packedOffset η j)| ≤ 2*R := by
  rw [show a-b+(packedOffset η i-packedOffset η j) =
    (a+packedOffset η i)-(b+packedOffset η j) by ring]
  linarith only [abs_sub (a+packedOffset η i) (b+packedOffset η j), hx i, hy j]

end GaussianChains.Clusters

