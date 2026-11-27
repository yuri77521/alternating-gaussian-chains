import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A finite discrete measure is determined by its nonnegative-frequency
moments on the complex circle. Node collisions are allowed throughout. -/
namespace GaussianChains
open Finset Polynomial

/-- Interpolate on distinct phase values rather than on distinct labels:
several labels may occupy exactly the same site. -/
private theorem interpolate_phase_values (T : Finset ℂ) (f : ℂ → ℂ) :
    ∃ p : Polynomial ℂ, ∀ w ∈ T, p.eval w = f w := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert z T hz ih =>
    obtain ⟨p, hp⟩ := ih
    let B : Polynomial ℂ := ∏ v ∈ T, (X - C v)
    have eB (w : ℂ) : B.eval w = ∏ v ∈ T, (w - v) := by simp [B, eval_prod]
    have nz : B.eval z ≠ 0 := by
      rw [eB]
      exact Finset.prod_ne_zero_iff.mpr fun v hv => sub_ne_zero.mpr (fun h => hz (h ▸ hv))
    refine ⟨p + C ((f z - p.eval z) / B.eval z) * B, ?_⟩
    intro w hw
    rw [eval_add, eval_mul, eval_C]
    rcases mem_insert.mp hw with rfl | hw
    · field_simp
      ring
    · rw [hp w hw, eB w, Finset.prod_eq_zero hw (sub_self w), mul_zero, add_zero]

/-- Once all Fourier moment equations hold, every test function on
the finite support has the same integral against the two signed measures. -/
theorem finite_dipole_moments {ι : Type*} [Fintype ι] (z c : ι → ℂ) (u v : ℂ)
    (hm : ∀ n : ℕ, ∑ i, c i * z i ^ n = u ^ n - v ^ n)
    (f : ℂ → ℂ) : ∑ i, c i * f (z i) = f u - f v := by
  classical
  let T : Finset ℂ := insert u (insert v (Finset.univ.image z))
  obtain ⟨p, hp⟩ := interpolate_phase_values T f
  have hpz (i : ι) : f (z i) = p.eval (z i) := (hp _ (by simp [T])).symm
  rw [← hp u (by simp [T]), ← hp v (by simp [T])]
  simp_rw [hpz, eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [mul_left_comm (c _) (p.coeff _)]
  rw [← Finset.mul_sum, hm, mul_sub]

/-- Singleton test functions read the net charge at each phase directly. -/
theorem net_charge_of_dipole_tests {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (u v : ℂ) (w : ℂ)
    (ht : ∀ f : ℂ → ℂ, ∑ i, c i * f (z i) = f u - f v) :
    (∑ i, if z i = w then c i else 0) =
      (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  classical
  simpa [mul_ite] using ht (fun t => if t = w then 1 else 0)

end GaussianChains
