import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Coordinates are lifts on the unit circle. No choice of cut at the origin
is required. The last labelled interval ends at the first site plus one. -/

noncomputable section
open Finset
namespace GaussianChains

def liftSite {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (n : ℕ) : ℝ :=
  x ⟨n % N, Nat.mod_lt n hN⟩ + (n / N : ℕ)

@[simp] theorem liftSite_fin {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N) :
    liftSite hN x i.val = x i := by
  simp [liftSite, Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt]

theorem liftSite_add_period {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (n : ℕ) :
    liftSite hN x (n + N) = liftSite hN x n + 1 := by
  simp [liftSite, Nat.add_div_right _ hN, add_assoc]

theorem liftSite_add_periods {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (n k : ℕ) :
    liftSite hN x (n + N * k) = liftSite hN x n + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, liftSite_add_period, ih]; push_cast; ring

def gap {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  liftSite hN x (i.val + 1) - liftSite hN x i.val

theorem gap_eq_lift_sub {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N) :
    gap hN x i = liftSite hN x (i.val + 1) - liftSite hN x i.val := rfl

theorem gap_lift_period {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (n : ℕ) :
    liftSite hN x (n+1) - liftSite hN x n = gap hN x ⟨n % N, Nat.mod_lt _ hN⟩ := by
  let r := n % N
  let k := n / N
  have hn : r + N*k = n := Nat.mod_add_div n N
  change _ = liftSite hN x (r+1) - liftSite hN x r
  conv_lhs => rw [← hn]
  rw [show r + N*k + 1 = (r+1) + N*k by omega, liftSite_add_periods, liftSite_add_periods]
  ring

theorem gap_interior {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N)
    (hi : i.val+1 < N) : gap hN x i = x ⟨i.val+1, hi⟩ - x i := by
  exact congrArg₂ (· - ·) (liftSite_fin hN x ⟨_,hi⟩) (liftSite_fin hN x i)

theorem gap_wrap {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N)
    (hi : i.val+1 = N) : gap hN x i = x ⟨0,hN⟩ + 1 - x i := by
  have hend := liftSite_add_period hN x 0
  rw [Nat.zero_add, (liftSite_fin hN x ⟨0,hN⟩ : liftSite hN x 0 = _)] at hend
  rw [gap, hi, hend, liftSite_fin]

theorem sum_gap {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    ∑ i, gap hN x i = 1 := by
  unfold gap
  rw [Fin.sum_univ_eq_sum_range (fun n => liftSite hN x (n+1) - liftSite hN x n),
    Finset.sum_range_sub]
  have hp := liftSite_add_period hN x 0
  rw [Nat.zero_add] at hp
  linarith

/-- The collision closure has floor zero. A positive floor imposes strict order. -/
def Feasible {N : ℕ} (hN : 0 < N) (h : ℝ) (x : Fin N → ℝ) : Prop :=
  ∀ i, h ≤ gap hN x i

def StrictlyOrdered {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) : Prop :=
  ∀ i, 0 < gap hN x i

theorem strict_of_feasible {N : ℕ} {hN : 0 < N} {h : ℝ} {x : Fin N → ℝ}
    (hh : 0 < h) (hx : Feasible hN h x) : StrictlyOrdered hN x :=
  fun i => lt_of_lt_of_le hh (hx i)

theorem floor_le_mean {N : ℕ} {hN : 0 < N} {h : ℝ} {x : Fin N → ℝ}
    (hx : Feasible hN h x) : h ≤ 1 / (N : ℝ) := by
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
    (fun i _ => hx i)
  rw [sum_gap hN x] at hb
  apply (le_div_iff₀ (Nat.cast_pos.mpr hN : 0 < (N : ℝ))).2
  simpa [mul_comm] using hb

/-- Physical coordinates with physical period L, lifted with the same labels. -/
def physicalLift {N : ℕ} (hN : 0 < N) (L : ℝ) (X : Fin N → ℝ) (n : ℕ) : ℝ :=
  X ⟨n % N, Nat.mod_lt n hN⟩ + L * (n / N : ℕ)

def physicalGap {N : ℕ} (hN : 0 < N) (L : ℝ) (X : Fin N → ℝ) (i : Fin N) : ℝ :=
  physicalLift hN L X (i.val+1) - physicalLift hN L X i.val

theorem physicalGap_normalize {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L)
    (X : Fin N → ℝ) (i : Fin N) :
    physicalGap hN L X i / L = gap hN (fun j => X j / L) i := by
  unfold physicalGap physicalLift gap liftSite
  field_simp [hL.ne']

theorem physicalFeasible_iff {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L)
    (floor : ℝ) (X : Fin N → ℝ) :
    (∀ i, floor ≤ physicalGap hN L X i) ↔ Feasible hN (floor/L) (fun j => X j/L) := by
  unfold Feasible
  simp_rw [← physicalGap_normalize hN hL X, div_le_div_iff_of_pos_right hL]

end GaussianChains
