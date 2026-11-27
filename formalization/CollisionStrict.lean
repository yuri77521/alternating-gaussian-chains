import CollisionDipole
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! A strictly ordered cell with more than two labels cannot realize the
net charges of a single dipole: none of its labels coincide on the circle. -/
namespace GaussianChains
open Real

theorem unitPhase_eq_imp_int {a b : ℝ} (h : unitPhase a = unitPhase b) :
    ∃ k : ℤ, a = b + k := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨k, ?_⟩
  have hi := congrArg Complex.im hk
  simp [Complex.mul_im, Complex.mul_re] at hi
  apply mul_left_cancel₀ (show (2*π : ℝ) ≠ 0 by positivity)
  linear_combination hi

theorem strictlyOrdered_phase_injective {N : ℕ} {hN : 0 < N} {x : Fin N → ℝ}
    (hx : StrictlyOrdered hN x) : Function.Injective (fun i => unitPhase (x i)) := by
  have hs : StrictMono (liftSite hN x) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h := hx ⟨n % N, Nat.mod_lt _ hN⟩
    rw [← gap_lift_period] at h
    linarith
  have ne {i j : Fin N} (hij : i < j) : unitPhase (x i) ≠ unitPhase (x j) := by
    intro eq
    obtain ⟨k, hk⟩ := unitPhase_eq_imp_int eq
    have a := hs (show i.val < j.val from hij)
    rw [liftSite_fin, liftSite_fin] at a
    have b := hs (show j.val < i.val + N by have := j.isLt; omega)
    rw [liftSite_add_period, liftSite_fin, liftSite_fin] at b
    have hk0 : (k : ℝ) < 0 := by linarith
    have hk1 : (-1 : ℝ) < k := by linarith
    have : k < 0 := by exact_mod_cast hk0
    have : (-1:ℤ) < k := by exact_mod_cast hk1
    omega
  intro i j eq
  rcases lt_trichotomy i j with h | h | h
  · exact (ne h eq).elim
  · exact h
  · exact (ne h eq.symm).elim

theorem RepresentsDipole.card_le_two_of_injective {N : ℕ} {x : Fin N → ℝ} {u : ℝ}
    (hx : RepresentsDipole x u) (hinj : Function.Injective fun i => unitPhase (x i)) :
    N ≤ 2 := by
  classical
  have side (i : Fin N) : unitPhase (x i) = unitPhase u ∨ unitPhase (x i) = -(unitPhase u) := by
    by_contra! hn
    have ht := hx (fun z => if z = unitPhase (x i) then 1 else 0)
    simp only [hinj.eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, if_neg hn.1.symm, if_neg hn.2.symm, sub_zero] at ht
    exact (by simp [charge] : (charge i : ℂ) ≠ 0) ht
  let c (i : Fin N) : Bool := decide (unitPhase (x i) = unitPhase u)
  have hc : Function.Injective c := by
    intro i j eq
    apply hinj
    by_cases hi : unitPhase (x i) = unitPhase u
    · by_cases hj : unitPhase (x j) = unitPhase u
      · exact hi.trans hj.symm
      · simp [c, hi, hj] at eq
    · by_cases hj : unitPhase (x j) = unitPhase u
      · simp [c, hi, hj] at eq
      · exact ((side i).resolve_left hi).trans ((side j).resolve_left hj).symm
  simpa using Fintype.card_le_of_injective c hc

theorem not_representsDipole_of_strict {N : ℕ} (h : 2 < N) {x : Fin N → ℝ}
    (hx : StrictlyOrdered (by omega) x) (u : ℝ) : ¬RepresentsDipole x u := by
  intro hd
  exact (not_le_of_gt h) (hd.card_le_two_of_injective (strictlyOrdered_phase_injective hx))

end GaussianChains
