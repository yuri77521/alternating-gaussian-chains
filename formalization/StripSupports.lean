import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

/-! The support lists here are the exact eighteen calls to `search` made by the
two width-band programs, in their iteration order. Reflection fixes gap five. -/
namespace GaussianChains.Strip

abbrev Support := Finset (Fin 5)

def offEdgeReps : List Support :=
  [{0}, {1}, {0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3},
   {0,1,2}, {0,1,3}, {0,1,4}, {0,2,3}, {0,2,4}, {1,2,3},
   {0,1,2,3}, {0,1,2,4}, {0,1,3,4}, {0,1,2,3,4}]

def reflectSupport (A : Support) : Support := A.image Fin.rev

/-- Every subset, including all lower-dimensional boundaries after contacts close. -/
theorem supports_exhaustive : ∀ A : Support,
    A = ∅ ∨ A = {2} ∨ A ∈ offEdgeReps ∨ reflectSupport A ∈ offEdgeReps := by decide

theorem offEdgeReps_distinct : offEdgeReps.length = 18 ∧ offEdgeReps.Nodup := by decide

theorem reflection_involutive (A : Support) : reflectSupport (reflectSupport A) = A := by
  simp [reflectSupport, Finset.image_image, Function.comp_def]

/-- Cyclic reindexing puts any specified (possibly tied) largest gap at index five. -/
def rotateGaps (u : Fin 6 → ℝ) (k i : Fin 6) : ℝ := u (i + k + 1)

theorem rotated_largest {u : Fin 6 → ℝ} {k : Fin 6} (hk : ∀ j, u j ≤ u k) :
    ∀ i, rotateGaps u k i ≤ rotateGaps u k 5 := by
  have index : (5 : Fin 6) + k + 1 = k := by fin_cases k <;> decide
  intro i
  simpa [rotateGaps, index] using hk (i+k+1)

noncomputable def activeSupport (u : Fin 6 → ℝ) : Support :=
  Finset.univ.filter fun i : Fin 5 => 0 < u i.castSucc

theorem mem_active_iff (u : Fin 6 → ℝ) (i : Fin 5) :
    i ∈ activeSupport u ↔ 0 < u i.castSucc := by simp [activeSupport]

theorem closedEdge_iff (u : Fin 6 → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (activeSupport u = ∅ ∨ activeSupport u = {2}) ↔
      ∀ i : Fin 5, i ≠ 2 → u i.castSucc = 0 := by
  constructor
  · intro h i hi
    apply le_antisymm _ (hu _)
    by_contra! hz
    have hm := (mem_active_iff u i).2 hz
    rcases h with he | he <;> simp [he, hi] at hm
  · intro h
    by_cases h2 : (2 : Fin 5) ∈ activeSupport u
    · right
      ext i
      by_cases hi : i = 2
      · subst i; simp [h2]
      · simp [mem_active_iff, h i hi, hi]
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i
      by_cases hi : i = 2
      · simpa [hi] using h2
      · simp [mem_active_iff, h i hi]

end GaussianChains.Strip
