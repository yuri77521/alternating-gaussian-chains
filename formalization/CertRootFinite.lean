import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Interval evaluation of the nine retained Gaussian derivative images at width 22.
The exponential enclosure is a parameter, so the proof also applies to other
certified evaluators with the same input range. -/

namespace GaussianChains.Root22
open scoped BigOperators

abbrev Box := ℚ × ℚ

def Encloses (b : Box) (y : ℝ) : Prop := (b.1 : ℝ) ≤ y ∧ y ≤ (b.2 : ℝ)

def scaleBox (v : ℚ) (b : Box) : Box :=
  if 0 ≤ v then (v*b.1, v*b.2) else (v*b.2, v*b.1)

theorem scaleBox_sound {b : Box} {y : ℝ} (hb : Encloses b y) (v : ℚ) :
    Encloses (scaleBox v b) ((v : ℝ)*y) := by
  rcases hb with ⟨hl, hu⟩
  by_cases h : 0 ≤ v
  · have hv : 0 ≤ (v : ℝ) := by exact_mod_cast h
    simpa [Encloses, scaleBox, h] using
      And.intro (mul_le_mul_of_nonneg_left hl hv) (mul_le_mul_of_nonneg_left hu hv)
  · have hv : (v : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    simpa [Encloses, scaleBox, h] using
      And.intro (mul_le_mul_of_nonpos_left hu hv) (mul_le_mul_of_nonpos_left hl hv)

def addBox (b c : Box) : Box := (b.1 + c.1, b.2 + c.2)
def subBox (b c : Box) : Box := (b.1 - c.2, b.2 - c.1)

theorem addBox_sound {b c : Box} {y z : ℝ} (hb : Encloses b y) (hc : Encloses c z) :
    Encloses (addBox b c) (y+z) := by
  simpa [Encloses, addBox] using And.intro (add_le_add hb.1 hc.1) (add_le_add hb.2 hc.2)

theorem subBox_sound {b c : Box} {y z : ℝ} (hb : Encloses b y) (hc : Encloses c z) :
    Encloses (subBox b c) (y-z) := by
  simpa [Encloses, subBox] using And.intro (sub_le_sub hb.1 hc.2) (sub_le_sub hb.2 hc.1)

def sumBox {ι : Type*} (s : Finset ι) (f : ι → Box) : Box :=
  (∑ i ∈ s, (f i).1, ∑ i ∈ s, (f i).2)

theorem sumBox_sound {ι : Type*} {s : Finset ι} {f : ι → Box} {g : ι → ℝ}
    (h : ∀ i ∈ s, Encloses (f i) (g i)) :
    Encloses (sumBox s f) (∑ i ∈ s, g i) := by
  unfold Encloses sumBox
  simp only [Rat.cast_sum]
  exact ⟨Finset.sum_le_sum (fun i hi => (h i hi).1), Finset.sum_le_sum (fun i hi => (h i hi).2)⟩

/-- Required behavior of the rational exponential enclosure. -/
def ExpBound (e : ℚ → Box) : Prop := ∀ {x}, 0 ≤ x → x ≤ 600 → Encloses (e x) (Real.exp (-(x:ℝ)))

def retained (e : ℚ → Box) (d : ℚ) : Box :=
  sumBox (Finset.Icc (-4:ℤ) 4) fun k =>
    scaleBox (-44*(d+k)) (e (22*(d+k)^2))

theorem retained_sound {e : ℚ → Box} (he : ExpBound e) {d : ℚ} (hd : -1 ≤ d ∧ d ≤ 1) :
    Encloses (retained e d)
      (∑ k ∈ Finset.Icc (-4:ℤ) 4,
        (-44*((d:ℝ)+k)) * Real.exp (-22*((d:ℝ)+k)^2)) := by
  apply sumBox_sound
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨hkl, hku⟩
  have hl : -4 ≤ (k:ℚ) := by exact_mod_cast hkl
  have hu : (k:ℚ) ≤ 4 := by exact_mod_cast hku
  have hz : 22*(d+k)^2 ≤ 600 := by
    nlinarith [mul_nonneg (show (0:ℚ) ≤ d+k+5 by linarith [hd.1])
      (show (0:ℚ) ≤ 5-(d+k) by linarith [hd.2])]
  have h := scaleBox_sound (he (x := 22*(d+k)^2) (by positivity) hz) (-44*(d+k))
  simpa only [Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_add, Rat.cast_intCast,
    Rat.cast_pow, neg_mul] using h

end GaussianChains.Root22
