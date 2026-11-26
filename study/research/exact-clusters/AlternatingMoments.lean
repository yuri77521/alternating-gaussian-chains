import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating moments of an odd block

The first `2*n+1` entries of `u` are the particle coordinates in one
cluster.  Equation (8) of the exact-contact manuscript holds for arbitrary
real coordinates.  The two gaps of pair `r` are indexed starting at zero.
-/

noncomputable section
open Finset

namespace AlternatingMoments

/-- Signed sum of the values of `f` at sites `0, ..., 2*n`. -/
def altSum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (2 * n + 1), (-1 : ℝ) ^ i * f i

def gapA (u : ℕ → ℝ) (r : ℕ) : ℝ := u (2 * r + 1) - u (2 * r)
def gapB (u : ℕ → ℝ) (r : ℕ) : ℝ := u (2 * r + 2) - u (2 * r + 1)

private theorem altSum_succ (f : ℕ → ℝ) (n : ℕ) :
    altSum f (n + 1) = altSum f n - f (2 * n + 1) + f (2 * n + 2) := by
  unfold altSum
  rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by omega,
    sum_range_succ, sum_range_succ]
  simp [pow_add, pow_mul]
  ring

theorem firstMoment (u : ℕ → ℝ) (n : ℕ) :
    altSum u n = u 0 + ∑ r ∈ range n, gapB u r := by
  induction n with
  | zero => simp [altSum]
  | succ n ih => rw [altSum_succ, ih, sum_range_succ]; unfold gapB; ring

private theorem endpoint (u : ℕ → ℝ) (n : ℕ) :
    u (2 * n) = altSum u n + ∑ r ∈ range n, gapA u r := by
  induction n with
  | zero => simp [altSum]
  | succ n ih =>
    rw [altSum_succ, sum_range_succ, show 2 * (n + 1) = 2 * n + 2 by omega]
    unfold gapA at *
    linarith

/-- The signed centered second moment is a quadratic polynomial in gaps. -/
theorem secondMoment (u : ℕ → ℝ) (n : ℕ) :
    altSum (fun i => u i ^ 2) n - (altSum u n) ^ 2 =
      2 * ∑ r ∈ range n, gapB u r * ∑ i ∈ range (r + 1), gapA u i := by
  induction n with
  | zero => simp [altSum]
  | succ n ih =>
    rw [altSum_succ, altSum_succ, sum_range_succ, sum_range_succ]
    have h := endpoint u n
    have hprefix : (∑ i ∈ range n, gapA u i) + gapA u n =
        u (2 * n + 1) - altSum u n := by
      unfold gapA at *
      linarith
    rw [hprefix, mul_add, ← ih]
    unfold gapB
    ring

/-- Fix the signed first moment `p` of a triple with adjacent gaps `a,b`. -/
def tripleVariance (p a b : ℝ) : ℝ :=
  (p - b) ^ 2 - (p - b + a) ^ 2 + (p + a) ^ 2 -
    ((p - b) - (p - b + a) + (p + a)) ^ 2

theorem tripleVariance_eq (p a b : ℝ) : tripleVariance p a b = 2 * a * b := by
  unfold tripleVariance
  ring

theorem triple_gap_derivatives (p a b η : ℝ) (ha : η ≤ a) (hb : η ≤ b) :
    HasDerivAt (fun t => tripleVariance p t b) (2 * b) a ∧
    HasDerivAt (fun t => tripleVariance p a t) (2 * a) b ∧
    2 * η ≤ 2 * b ∧ 2 * η ≤ 2 * a := by
  simp only [tripleVariance_eq]
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · simpa using (((hasDerivAt_id a).const_mul 2).mul_const b)
  · simpa using ((hasDerivAt_id b).const_mul (2 * a))

#print axioms firstMoment
#print axioms secondMoment
#print axioms tripleVariance_eq
#print axioms triple_gap_derivatives

end AlternatingMoments
