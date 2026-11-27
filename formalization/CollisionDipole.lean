import ChainScore
import ChainFourier
import ChainGeometry

/-! Cancellation in a labelled collision cell. The pushforward signed
measure is tested on phases, so labels lifted a full period apart coincide. -/

noncomputable section
namespace GaussianChains
open Real

def unitPhase (u : ℝ) : ℂ := Complex.exp ((2*π*u : ℝ) * Complex.I)

/-- After combining coincident sites, unit positive and negative masses remain
at antipodal phases. The orientation records which sign is at which point. -/
def RepresentsDipole {N : ℕ} (x : Fin N → ℝ) (u : ℝ) : Prop :=
  ∀ f : ℂ → ℂ, (∑ i, (charge i : ℂ) * f (unitPhase (x i))) =
    f (unitPhase u) - f (-(unitPhase u))

theorem unitPhase_add_half (u : ℝ) : unitPhase (u+1/2) = -(unitPhase u) := by
  unfold unitPhase
  rw [show 2*π*(u+1/2) = 2*π*u + π by ring]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

theorem structureFactor_eq_phase_powers {N : ℕ} (x : Fin N → ℝ) (n : ℕ) :
    structureFactor x n = ∑ i, (charge i : ℂ) * (unitPhase (x i))^n := by
  unfold structureFactor unitPhase
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem RepresentsDipole.structureFactor {N : ℕ} {x : Fin N → ℝ} {u : ℝ}
    (hx : RepresentsDipole x u) (n : ℕ) :
    structureFactor x n = (unitPhase u)^n - (-(unitPhase u))^n := by
  rw [structureFactor_eq_phase_powers]
  exact hx (·^n)

/-- One positive label at u and all the others at u+1/2. For even N the
total charge there is minus one, irrespective of the number of neutral pairs. -/
def dipoleTrial {N : ℕ} (hN : 0 < N) (u : ℝ) (i : Fin N) : ℝ :=
  if i = ⟨0,hN⟩ then u else u+1/2

private theorem sum_dipoleTrial {R : Type*} [CommRing R] {N : ℕ} (hN : 0 < N)
    (u : ℝ) (w : Fin N → R) (hw : ∑ i, w i = 0) (h0 : w ⟨0,hN⟩ = 1) (f : ℝ → R) :
    (∑ i, w i * f (dipoleTrial hN u i)) = f u - f (u+1/2) := by
  classical
  have term (i : Fin N) : w i * f (dipoleTrial hN u i) =
      w i * f (u+1/2) + if i = ⟨0,hN⟩ then f u - f (u+1/2) else 0 := by
    by_cases hi : i = ⟨0,hN⟩
    · simp [dipoleTrial, hi, h0]
    · simp [dipoleTrial, hi]
  simp_rw [term, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hw]
  simp

theorem dipoleTrial_represents (m : ℕ) (hN : 0 < 2*m) (u : ℝ) :
    RepresentsDipole (dipoleTrial hN u) u := by
  intro f
  rw [← unitPhase_add_half]
  apply sum_dipoleTrial hN u (fun i => (charge i : ℂ)) _ _ (fun t => f (unitPhase t))
  · simpa using congrArg Complex.ofReal (charge_sum_even m)
  · simp [charge]

theorem dipoleTrial_feasible (m : ℕ) (hN : 0 < 2*m) (u : ℝ) :
    Feasible hN 0 (dipoleTrial hN u) := by
  intro i
  by_cases hl : i.val+1 = 2*m
  · rw [gap_wrap hN _ i hl]
    have hi : i ≠ ⟨0,hN⟩ := by
      intro h
      subst i
      simp at hl
      omega
    simp [dipoleTrial, hi]
    linarith
  · have hi' : i.val+1 < 2*m := by have := i.isLt; omega
    rw [gap_interior hN _ i hi']
    have hj : (⟨i.val+1,hi'⟩ : Fin (2*m)) ≠ ⟨0,hN⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    by_cases hi : i = ⟨0,hN⟩ <;> simp [dipoleTrial, hj, hi]

theorem dipoleTrial_energy (m : ℕ) (hN : 0 < 2*m) (u s : ℝ) :
    imageEnergy s (dipoleTrial hN u) =
      1 - 2*(kernel s 0 - kernel s (1/2))/((2*m : ℕ) : ℝ) := by
  let x := dipoleTrial hN u
  have signed (f : ℝ → ℝ) : (∑ i, charge i * f (x i)) = f u - f (u+1/2) :=
    sum_dipoleTrial hN u charge (charge_sum_even m) (by simp [charge]) f
  have pair (i : Fin (2*m)) : (∑ j, charge i*charge j*kernel s (x j-x i)) =
      charge i*(kernel s (u-x i)-kernel s (u+1/2-x i)) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [signed (fun t => kernel s (t - x i))]
  unfold imageEnergy
  change 1 - _ * (∑ i, ∑ j, charge i*charge j*kernel s (x j-x i)) = _
  simp_rw [pair]
  rw [signed (fun t => kernel s (u-t)-kernel s (u+1/2-t))]
  simp only [sub_self, add_sub_cancel_left, sub_add_cancel_left]
  rw [kernel_neg]
  ring

/-- Sufficiency direction of the collision-closure equality description.
The width restriction enters the converse and the ground-state lower bound. -/
theorem RepresentsDipole.imageEnergy (m : ℕ) (hN : 0 < 2*m) {x : Fin (2*m) → ℝ}
    {u s : ℝ} (hx : RepresentsDipole x u) (hs : 0 < s) :
    imageEnergy s x = 1 - 2*(kernel s 0 - kernel s (1/2))/((2*m : ℕ) : ℝ) := by
  rw [← dipoleTrial_energy m hN u s, imageEnergy_fourier m hs, imageEnergy_fourier m hs]
  simp_rw [hx.structureFactor, (dipoleTrial_represents m hN u).structureFactor]

end GaussianChains
