import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Four radius charts for the angular integral with semicircle endpoints at zero and π. -/
noncomputable section
namespace GaussianChains.Localization
open Real MeasureTheory Set

def quadrantAngle (i : Fin 4) (t : ℝ) : ℝ :=
  match i.val with
  | 0 => t
  | 1 => π - t
  | 2 => π + t
  | _ => 2 * π - t

variable {E : Type*} [NormedAddCommGroup E]

theorem quadrant_intervalIntegrable (f : ℝ → E) (hf : ∀ a b, IntervalIntegrable f volume a b)
    (i : Fin 4) : IntervalIntegrable (fun t => f (quadrantAngle i t)) volume 0 (π/2) := by
  fin_cases i
  · exact hf _ _
  · change IntervalIntegrable (fun t => f (π - t)) volume 0 (π/2)
    convert (hf π (π - π/2)).comp_sub_left π using 1 <;> ring
  · change IntervalIntegrable (fun t => f (π + t)) volume 0 (π/2)
    convert (hf π (π + π/2)).comp_add_left π using 1 <;> ring
  · change IntervalIntegrable (fun t => f (2*π - t)) volume 0 (π/2)
    convert (hf (2*π) (2*π - π/2)).comp_sub_left (2*π) using 1 <;> ring

variable [NormedSpace ℝ E]

theorem integral_upper_quadrants (f : ℝ → E) (hf : ∀ a b, IntervalIntegrable f volume a b) :
    (∫ u in 0..π, f u) = (∫ t in 0..π/2, f (quadrantAngle 0 t)) +
      ∫ t in 0..π/2, f (quadrantAngle 1 t) := by
  change _ = (∫ t in 0..π/2, f t) + ∫ t in 0..π/2, f (π - t)
  rw [intervalIntegral.integral_comp_sub_left, sub_zero, show π - π/2 = π/2 by ring,
    intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _)]

theorem integral_quadrants (f : ℝ → E) (hf : ∀ a b, IntervalIntegrable f volume a b) :
    (∫ u in 0..2*π, f u) = ∑ i : Fin 4, ∫ t in 0..π/2, f (quadrantAngle i t) := by
  rw [Fin.sum_univ_four]
  change _ = (∫ t in 0..π/2, f t) + (∫ t in 0..π/2, f (π - t)) +
    (∫ t in 0..π/2, f (π + t)) + ∫ t in 0..π/2, f (2*π - t)
  rw [intervalIntegral.integral_comp_sub_left, intervalIntegral.integral_comp_add_left,
    intervalIntegral.integral_comp_sub_left, add_zero, sub_zero, sub_zero,
    show π - π/2 = π/2 by ring, show 2*π - π/2 = π + π/2 by ring,
    intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _),
    intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _),
    intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _)]

/-- Occupancy of a measurable collection of intervals (or an arbitrary measurable set). -/
def occupied (A : Set ℝ) (t : ℝ) : ℝ := A.indicator (fun _ => 1) t

theorem occupied_mem_Icc (A : Set ℝ) (t : ℝ) : occupied A t ∈ Icc 0 1 := by
  by_cases ht : t ∈ A <;> simp [occupied, ht]

theorem occupied_intervalIntegrable {A : Set ℝ} (hA : MeasurableSet A) (a b : ℝ) :
    IntervalIntegrable (occupied A) volume a b := by
  rw [intervalIntegrable_iff]
  change Integrable (A.indicator (fun _ : ℝ => (1:ℝ))) _
  apply Integrable.indicator _ hA
  exact (intervalIntegrable_iff.mp (intervalIntegrable_const (a := a) (b := b)))

end GaussianChains.Localization
