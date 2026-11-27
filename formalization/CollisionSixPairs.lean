import CollisionDipole
import Mathlib.Data.Multiset.Count
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! At N = 6, test-function cancellation means exactly two coincident
opposite-charge pairs, with multiplicity. Neither pair is required to avoid
the other pair or the two net charges. -/

noncomputable section
namespace GaussianChains
open Multiset

def positivePhases (x : Fin 6 → ℝ) : Multiset ℂ :=
  unitPhase (x 0) ::ₘ unitPhase (x 2) ::ₘ unitPhase (x 4) ::ₘ 0

def negativePhases (x : Fin 6 → ℝ) : Multiset ℂ :=
  unitPhase (x 1) ::ₘ unitPhase (x 3) ::ₘ unitPhase (x 5) ::ₘ 0

private theorem six_test_sum (x : Fin 6 → ℝ) (f : ℂ → ℂ) :
    (∑ i, (charge i : ℂ) * f (unitPhase (x i))) =
      ((positivePhases x).map f).sum - ((negativePhases x).map f).sum := by
  norm_num [Fin.sum_univ_six, positivePhases, negativePhases, charge]
  ring

private theorem multiset_eq_of_test {S T : Multiset ℂ}
    (h : ∀ f : ℂ → ℂ, (S.map f).sum = (T.map f).sum) : S = T := by
  classical
  apply Multiset.ext.mpr
  intro z
  let d (a : ℂ) : ℂ := if z = a then 1 else 0
  have mass (s : Multiset ℂ) : (s.map d).sum = (s.count z : ℂ) := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons, Nat.cast_add, ih]
      by_cases ha : z = a <;> simp [ha, d, add_comm]
  have hc := h d
  rw [mass, mass] at hc
  exact_mod_cast hc

theorem representsDipole_iff_two_neutral_pairs (x : Fin 6 → ℝ) (u : ℝ) :
    RepresentsDipole x u ↔ ∃ r : Multiset ℂ, r.card = 2 ∧
      positivePhases x = unitPhase u ::ₘ r ∧ negativePhases x = (-(unitPhase u)) ::ₘ r := by
  constructor
  · intro h
    let z := unitPhase u
    have hne : z ≠ -z := by
      intro hz
      have hz0 : z = 0 := by linear_combination hz / 2
      exact (Complex.exp_ne_zero _) hz0
    have hc : (-z) ::ₘ positivePhases x = z ::ₘ negativePhases x := by
      apply multiset_eq_of_test
      intro f
      have ht := h f
      rw [six_test_sum] at ht
      simp only [Multiset.map_cons, Multiset.sum_cons]
      dsimp only [z]
      linear_combination ht
    have mem : z ∈ positivePhases x := by
      have hh : z ∈ (-z) ::ₘ positivePhases x := by
        rw [hc]
        exact Multiset.mem_cons_self _ _
      exact (Multiset.mem_cons.mp hh).resolve_left hne
    obtain ⟨r, hr⟩ := Multiset.exists_cons_of_mem mem
    have hn : negativePhases x = (-z) ::ₘ r := by
      rw [hr, Multiset.cons_swap] at hc
      exact ((Multiset.cons_inj_right z).mp hc).symm
    refine ⟨r, ?_, hr, hn⟩
    have hh := congrArg Multiset.card hr
    simp [positivePhases] at hh
    omega
  · rintro ⟨r, _, hp, hn⟩ f
    rw [six_test_sum, hp, hn]
    simp

end GaussianChains
