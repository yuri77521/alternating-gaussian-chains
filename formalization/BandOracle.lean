import CertTree
import CertTreeSimplex
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

/-! Geometric and signed interval operations for the 18 support trees.
The width and the floor are intervals independent of the slack simplex. -/
namespace GaussianChains.Band
open GaussianChains.Cert
open Finset Interval

def corners (I J : Interval) (f : ℚ → ℚ → ℚ) : Interval :=
  ⟨min (min (f I.lo J.lo) (f I.lo J.hi)) (min (f I.hi J.lo) (f I.hi J.hi)),
   max (max (f I.lo J.lo) (f I.lo J.hi)) (max (f I.hi J.lo) (f I.hi J.hi))⟩

private theorem between_linear {l x h a b L H : ℝ} (hx : l ≤ x ∧ x ≤ h)
    (hl : L ≤ a*l+b ∧ a*l+b ≤ H) (hh : L ≤ a*h+b ∧ a*h+b ≤ H) :
    L ≤ a*x+b ∧ a*x+b ≤ H := by
  rcases le_total 0 a with ha | ha
  · exact ⟨hl.1.trans (add_le_add_left (mul_le_mul_of_nonneg_left hx.1 ha) _),
           (add_le_add_left (mul_le_mul_of_nonneg_left hx.2 ha) _).trans hh.2⟩
  · exact ⟨hh.1.trans (add_le_add_left (mul_le_mul_of_nonpos_left hx.2 ha) _),
           (add_le_add_left (mul_le_mul_of_nonpos_left hx.1 ha) _).trans hl.2⟩

private theorem corners_mem (I J : Interval) (f : ℚ → ℚ → ℚ)
    {x y : ℚ} (hx : x = I.lo ∨ x = I.hi) (hy : y = J.lo ∨ y = J.hi) :
    (corners I J f).Mem ((f x y : ℚ) : ℝ) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [corners, Mem]

/-- Span is the number of gaps in the arc; u is the sum of their slack coordinates. -/
def distanceRange (s : ℕ) (floor arc : Interval) : Interval :=
  corners floor arc (fun h u => s*h + (1-6*h)*u)

theorem distanceRange_mem (s : ℕ) {floor arc : Interval} {h u : ℝ}
    (hh : floor.Mem h) (hu : arc.Mem u) :
    (distanceRange s floor arc).Mem (s*h + (1-6*h)*u) := by
  let I := distanceRange s floor arc
  have row (a : ℚ) (ha : a = floor.lo ∨ a = floor.hi) :
      I.Mem (s*(a:ℝ)+(1-6*(a:ℝ))*u) := by
    have cell (b : ℚ) (hb : b = arc.lo ∨ b = arc.hi) :
        I.Mem ((1-6*(a:ℝ))*(b:ℝ)+s*a) := by
      have hc := corners_mem floor arc (fun t v => (s:ℚ)*t+(1-6*t)*v) ha hb
      push_cast at hc
      rw [add_comm]
      exact hc
    rw [add_comm]
    exact between_linear hu (cell _ (Or.inl rfl)) (cell _ (Or.inr rfl))
  have hrow (a : ℚ) (ha : a = floor.lo ∨ a = floor.hi) :
      I.Mem (((s:ℝ)-6*u)*(a:ℝ)+u) := by
    convert row a ha using 1 <;> ring
  rw [show (s:ℝ)*h+(1-6*h)*u = ((s:ℝ)-6*u)*h+u by ring]
  exact between_linear (a := (s:ℝ)-6*u) (b := u) hh
    (hrow _ (Or.inl rfl)) (hrow _ (Or.inr rfl))

def arc (i j : Fin 6) : Finset (Fin 6) := Finset.Ico i j

def pairRange (floor : Interval) (B : Box 6) (i j : Fin 6) : Interval :=
  distanceRange (j.val-i.val) floor (B.arcBound (arc i j) 1)

/-- A band table query covers every pair displacement at once, including closed endpoints. -/
theorem pairRange_mem {floor : Interval} {B : Box 6} {h : ℝ} {u : Fin 6 → ℝ}
    (hh : floor.Mem h) (hu : B.Mem u) (hs : ∑ k, u k = 1) (i j : Fin 6) :
    (pairRange floor B i j).Mem
      (((j.val-i.val:ℕ):ℝ)*h + (1-6*h)*(∑ k ∈ arc i j, u k)) :=
  distanceRange_mem _ hh (Box.arcBound_mem hu (by simpa using hs) _)

/-- Sum a finite expression of signed terms, as in the value, cut-gradient and
cut-curvature tests. A negative summand reverses both endpoints. -/
def sumRange {ι : Type} (A : Finset ι) (I : ι → Interval) : Interval :=
  ⟨∑ k ∈ A, (I k).lo, ∑ k ∈ A, (I k).hi⟩

theorem sumRange_mem {ι : Type} {A : Finset ι} {I : ι → Interval} {v : ι → ℝ}
    (hv : ∀ i ∈ A, (I i).Mem (v i)) : (sumRange A I).Mem (∑ k ∈ A, v k) := by
  simpa [sumRange, Interval.Mem] using And.intro (sum_le_sum fun i hi => (hv i hi).1)
      (sum_le_sum fun i hi => (hv i hi).2)

end GaussianChains.Band
