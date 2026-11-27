import CertTree
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! A continuous terminal from the frozen width-22 atlas. The coordinates are
the block starts of word 111111 in units of 1/32000. The reference verifier
visits this box at node 3. Cyclic symmetry chooses the wrapping gap as largest
among the six singleton starts. Its upper bound is smaller than the lower
bound for the first gap throughout the box. -/
namespace GaussianChains.Cert.AtlasExample
open Interval

def box : Box 6 :=
  ![⟨0,0⟩, ⟨23888/32000,31840/32000⟩, ⟨23920/32000,31872/32000⟩,
    ⟨23952/32000,31904/32000⟩, ⟨23984/32000,31936/32000⟩, ⟨24016/32000,31968/32000⟩]

/-- Last gap minus first gap, in the unit-period gauge with lifted positions. -/
def orderMargin (x : Fin 6 → ℝ) : ℝ := (1 + x 0 - x 5) - (x 1 - x 0)

def orderBound (B : Box 6) : Interval :=
  (((singleton 1).add (B 0)).add (B 5).neg).add (((B 1).add (B 0).neg).neg)

theorem orderBound_mem {B : Box 6} {x : Fin 6 → ℝ} (hx : B.Mem x) :
    (orderBound B).Mem (orderMargin x) := by
  simpa [orderBound, orderMargin, sub_eq_add_neg] using
    add_mem (add_mem (add_mem (singleton_mem 1) (hx 0)) (neg_mem (hx 5)))
      (neg_mem (add_mem (hx 1) (neg_mem (hx 0))))

def bounds (B : Box 6) : Quantity → Interval
  | .feasible _ => orderBound B
  | _ => singleton 0

private def value (x : Fin 6 → ℝ) : Quantity → ℝ
  | .feasible _ => orderMargin x
  | _ => 0

def orderLeaf : Tree 6 := .leaf (.feasible 0)
def splitCert : Tree 6 := .split 2 (26000/32000) orderLeaf orderLeaf

theorem extracted_leaf_accepted : accept bounds none box orderLeaf = true := by decide +kernel
theorem refined_leaf_accepted : accept bounds none box splitCert = true := by decide +kernel
theorem missing_child_rejected :
    accept bounds none box (.split 2 (26000/32000) orderLeaf .hole) = false := by decide +kernel

theorem extracted_leaf_excludes {x : Fin 6 → ℝ} (hx : box.Mem x) :
    ¬ (x 1 - x 0 ≤ 1 + x 0 - x 5) := by
  intro h
  have hc : 0 ≤ orderMargin x := sub_nonneg.mpr h
  apply accept_sound (value := value) (candidate := fun y => 0 ≤ orderMargin y)
    (target := none) (bounds := bounds) (t := splitCert) (B := box) (x := x)
    (h := refined_leaf_accepted) (hx := hx) (hc := hc)
  · intro B y hy _ k
    cases k with
    | feasible _ => exact orderBound_mem hy
    | _ => simpa [bounds, value] using singleton_mem 0
  · intro y hy k
    cases k <;> simp_all [Necessary, value]

/-- The chosen rational box does contain physically feasible ordered positions with
positive floor 1/1000. The cyclic-largest constraint drives this pruning step. -/
theorem extracted_leaf_has_ordered_point :
    ∃ x : Fin 6 → ℝ, box.Mem x ∧
    (∀ i : Fin 5, 1/1000 ≤ x i.succ - x i.castSucc) ∧
    1/1000 ≤ 1 + x 0 - x 5 := by
  refine ⟨![0, 3/4, 4/5, 17/20, 9/10, 19/20], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [box, Interval.Mem, Matrix.cons_val]
  · intro i
    fin_cases i
    · change (1/1000:ℝ) ≤ 3/4 - 0; norm_num
    · change (1/1000:ℝ) ≤ 4/5 - 3/4; norm_num
    · change (1/1000:ℝ) ≤ 17/20 - 4/5; norm_num
    · change (1/1000:ℝ) ≤ 9/10 - 17/20; norm_num
    · change (1/1000:ℝ) ≤ 19/20 - 9/10; norm_num
  · change (1/1000:ℝ) ≤ 1 + 0 - 19/20
    norm_num

#print axioms extracted_leaf_excludes
#print axioms missing_child_rejected

end GaussianChains.Cert.AtlasExample