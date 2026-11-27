import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The entire family (8), including both contact endpoints and the uniform endpoint. -/
noncomputable section

namespace GaussianChains.PackedFace
open Set

def sites (h t : ℝ) : Fin 6 → ℝ :=
  ![0, h, 2*h, 1/2+t, 1/2+t+h, 1/2+t+2*h]

def bound (h : ℝ) : ℝ := 1/2 - 3*h

def feasible (h t : ℝ) : Prop := |t| ≤ bound h

/-- Squared-displacement coordinate used in (9). -/
def coord (t : ℝ) : ℝ := 1 - Real.cos (2*Real.pi*t)

theorem feasible_iff_outer_gaps (h t : ℝ) :
    feasible h t ↔ h ≤ sites h t 3 - sites h t 2 ∧
      h ≤ 1 + sites h t 0 - sites h t 5 := by
  change |t| ≤ 1/2 - 3*h ↔ h ≤ 1/2+t-2*h ∧ h ≤ 1+0-(1/2+t+2*h)
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem inner_gaps (h t : ℝ) :
    sites h t 1 - sites h t 0 = h ∧ sites h t 2 - sites h t 1 = h ∧
    sites h t 4 - sites h t 3 = h ∧ sites h t 5 - sites h t 4 = h := by
  change h-0 = h ∧ 2*h-h = h ∧ 1/2+t+h-(1/2+t) = h ∧ 1/2+t+2*h-(1/2+t+h) = h
  exact ⟨by ring, by ring, by ring, by ring⟩

theorem positive_endpoint_wrap_contact (h : ℝ) :
    1 + sites h (bound h) 0 - sites h (bound h) 5 = h := by
  change 1+0-(1/2+(1/2-3*h)+2*h) = h
  ring

theorem negative_endpoint_middle_contact (h : ℝ) :
    sites h (-bound h) 3 - sites h (-bound h) 2 = h := by
  change 1/2+ -(1/2-3*h) - 2*h = h
  ring

@[simp] theorem feasible_one_sixth_iff (t : ℝ) : feasible (1/6) t ↔ t = 0 := by
  norm_num [feasible, bound]

@[simp] theorem coord_zero : coord 0 = 0 := by simp [coord]

@[simp] theorem coord_neg (t : ℝ) : coord (-t) = coord t := by simp [coord]

@[simp] theorem coord_abs (t : ℝ) : coord |t| = coord t := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, coord_neg]

theorem continuous_coord : Continuous coord := by
  unfold coord
  fun_prop

theorem strictMonoOn_coord : StrictMonoOn coord (Icc 0 (1/2 : ℝ)) := by
  intro x hx y hy hxy
  have ha (v : ℝ) (hv : v ∈ Icc 0 (1/2 : ℝ)) : 2*Real.pi*v ∈ Icc 0 Real.pi := by
    constructor
    · exact mul_nonneg (by positivity) hv.1
    · nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hv.2)]
  have hc := Real.strictAntiOn_cos (ha x hx) (ha y hy)
    (mul_lt_mul_of_pos_left hxy (by positivity))
  exact sub_lt_sub_left hc _

private theorem bound_mem {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1/6) :
    bound h ∈ Icc 0 (1/2 : ℝ) := by
  unfold bound
  constructor <;> linarith

theorem coord_image (h : ℝ) (hh : 0 ≤ h) (hh' : h ≤ 1/6) :
    coord '' Icc 0 (bound h) = Icc 0 (coord (bound h)) := by
  have hb := bound_mem hh hh'
  have hmon := strictMonoOn_coord.monotoneOn.mono (Icc_subset_Icc_right hb.2)
  have h₀ : (0:ℝ) ∈ Icc 0 (bound h) := ⟨le_rfl,hb.1⟩
  have h₁ : bound h ∈ Icc 0 (bound h) := ⟨hb.1,le_rfl⟩
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    exact ⟨by simpa using hmon h₀ ht ht.1, hmon ht h₁ ht.2⟩
  · simpa using intermediate_value_Icc hb.1 continuous_coord.continuousOn

theorem coord_eq_iff_abs_eq {h t u : ℝ} (hh : 0 ≤ h) (ht : feasible h t) (hu : feasible h u) :
    coord t = coord u ↔ |t| = |u| := by
  have hb : bound h ≤ 1/2 := by unfold bound; linarith
  rw [← coord_abs t, ← coord_abs u]
  constructor
  · exact strictMonoOn_coord.injOn ⟨abs_nonneg _, ht.trans hb⟩ ⟨abs_nonneg _, hu.trans hb⟩
  · exact congrArg coord

/-- Reflection is the only ambiguity of the squared-displacement coordinate. -/
theorem coord_eq_iff_reflection {h t u : ℝ} (hh : 0 ≤ h) (ht : feasible h t)
    (hu : feasible h u) : coord t = coord u ↔ t = u ∨ t = -u := by
  rw [coord_eq_iff_abs_eq hh ht hu, abs_eq_abs]

end GaussianChains.PackedFace


