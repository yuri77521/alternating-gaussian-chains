import CertTree
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Closed-box bounds with a prescribed sum and a distinguished largest
coordinate, as used in the width-strip simplex certificate. -/
namespace GaussianChains.Cert.Box
open Interval

def partialSum (B : Box d) (A : Finset (Fin d)) : Interval :=
  ⟨∑ i ∈ A, (B i).lo, ∑ i ∈ A, (B i).hi⟩

theorem partialSum_mem {B : Box d} {x : Fin d → ℝ} (hx : B.Mem x) (A : Finset (Fin d)) :
    (B.partialSum A).Mem (∑ i ∈ A, x i) := by
  simpa [partialSum, Interval.Mem] using
    And.intro (Finset.sum_le_sum (s:=A) (fun i _ => (hx i).1))
      (Finset.sum_le_sum (s:=A) (fun i _ => (hx i).2))

def arcBound (B : Box d) (A : Finset (Fin d)) (total : ℚ) : Interval :=
  (B.partialSum A).meet ((singleton total).add (B.partialSum Aᶜ).neg)

theorem arcBound_mem {B : Box d} {x : Fin d → ℝ} {total : ℚ} (hx : B.Mem x)
    (hs : ∑ i, x i = (total:ℝ)) (A : Finset (Fin d)) :
    (B.arcBound A total).Mem (∑ i ∈ A, x i) := by
  apply meet_mem (partialSum_mem hx A)
  have hcomp := add_mem (singleton_mem total) (neg_mem (partialSum_mem hx Aᶜ))
  have hsplit := Finset.sum_add_sum_compl A x
  rw [hs] at hsplit
  convert hcomp using 1
  linarith

def tightenTotal (B : Box d) (total : ℚ) : Box d := fun i => B.arcBound {i} total

theorem tightenTotal_mem {B : Box d} {x : Fin d → ℝ} {total : ℚ}
    (hx : B.Mem x) (hs : ∑ i, x i = (total:ℝ)) : (B.tightenTotal total).Mem x := by
  intro i
  simpa [tightenTotal] using arcBound_mem hx hs {i}

def tightenLargest (B : Box d) (largest other : Fin d) : Box d := fun i =>
  ⟨if i = largest then max (B i).lo (B other).lo else (B i).lo,
   if i = other then min (B i).hi (B largest).hi else (B i).hi⟩

theorem tightenLargest_mem {B : Box d} {x : Fin d → ℝ} {k j : Fin d}
    (hx : B.Mem x) (hkj : x j ≤ x k) : (B.tightenLargest k j).Mem x := by
  intro i
  constructor
  · by_cases e : i = k
    · subst i
      simpa [tightenLargest] using max_le (hx k).1 ((hx j).1.trans hkj)
    · simpa [tightenLargest, e] using (hx i).1
  · by_cases e : i = j
    · subst i
      simpa [tightenLargest] using le_min (hx j).2 (hkj.trans (hx k).2)
    · simpa [tightenLargest, e] using (hx i).2

/-- Successive contractions are safe at a tied maximum as well. -/
def chamber (B : Box d) (total : ℚ) (largest : Fin d) (others : List (Fin d)) : Box d :=
  others.foldl (fun C j => C.tightenLargest largest j) (B.tightenTotal total)

theorem chamber_mem {B : Box d} {x : Fin d → ℝ} {total : ℚ} {k : Fin d}
    (hx : B.Mem x) (hs : ∑ i, x i = (total:ℝ)) (hk : ∀ j, x j ≤ x k)
    (others : List (Fin d)) : (B.chamber total k others).Mem x := by
  have step (js : List (Fin d)) (C : Box d) (hm : C.Mem x) :
      (js.foldl (fun D j => D.tightenLargest k j) C).Mem x := by
    induction js generalizing C with
    | nil => exact hm
    | cons j js ih => exact ih _ (tightenLargest_mem hm (hk j))
  exact step others _ (tightenTotal_mem hx hs)

def emptyB (B : Box d) : Bool := decide (∃ i, (B i).hi < (B i).lo)

theorem emptyB_sound {B : Box d} (h : emptyB B = true) (x : Fin d → ℝ) : ¬ B.Mem x := by
  obtain ⟨i,hi⟩ : ∃ i, (B i).hi < (B i).lo := of_decide_eq_true h
  intro hx
  exact (not_lt_of_ge ((hx i).1.trans (hx i).2)) (by exact_mod_cast hi)

end GaussianChains.Cert.Box
