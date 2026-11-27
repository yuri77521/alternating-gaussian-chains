import CollisionDipole
import CollisionMoments
import ClustersLocalizationModes

/-! Equality in the semicircle deficit determines the signed mass at
every phase, even when several labels coincide. -/
noncomputable section
namespace GaussianChains
open Real MeasureTheory Set Localization

theorem representsDipole_iff_structureFactor {N : ℕ} (x : Fin N → ℝ) (u : ℝ) :
    RepresentsDipole x u ↔ ∀ n : ℕ,
      structureFactor x n = unitPhase u ^ n - (-(unitPhase u)) ^ n := by
  refine ⟨fun h => h.structureFactor, fun h f => ?_⟩
  apply finite_dipole_moments
  intro n
  rw [← structureFactor_eq_phase_powers, h n]

theorem RepresentsDipole.net_charge {N : ℕ} {x : Fin N → ℝ} {u : ℝ}
    (h : RepresentsDipole x u) (z : ℂ) :
    (∑ i, if unitPhase (x i) = z then (charge i : ℂ) else 0) =
      (if unitPhase u = z then 1 else 0) - (if -(unitPhase u) = z then 1 else 0) :=
  net_charge_of_dipole_tests _ _ _ _ z h

private theorem unitPhase_add' (u v : ℝ) : unitPhase (u+v) = unitPhase u * unitPhase v := by
  unfold unitPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem representsDipole_of_translate {N : ℕ} (x : Fin N → ℝ) (a : ℝ)
    (h : RepresentsDipole (fun i => x i - a) 0) : RepresentsDipole x a := by
  intro f
  have ht := h (fun z => f (z * unitPhase a))
  simp only [← unitPhase_add', sub_add_cancel, zero_add, neg_mul] at ht
  simpa only [← unitPhase_add', zero_add] using ht

theorem arcMode_eq_dipole_of_zero_cost (d : Fin 4 → ℝ → ℝ)
    (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t ∧ d i t ≤ 1)
    (h0 : arcCost d = 0) (n : ℕ) : arcMode n d = dipoleMode n := by
  have hm : arcMass d ^ 2 ≤ 4 * π * arcCost d := discrepancy_mass_sq_le d hi hd
  rw [h0, mul_zero] at hm
  have hmass : arcMass d = 0 := by nlinarith [sq_nonneg (arcMass d)]
  have hz := modeChange_norm n d hi (fun i t ht => (hd i t ht).1)
  rw [hmass, mul_zero, norm_le_zero_iff] at hz
  rw [arcMode, hz, add_zero]

theorem representsDipole_of_zero_cost {m : ℕ} (x : Fin (2*m) → ℝ)
    (d : Fin 4 → ℝ → ℝ) (hi : ∀ i, IntervalIntegrable (d i) volume 0 (π/2))
    (hd : ∀ i t, t ∈ Icc 0 (π/2) → 0 ≤ d i t ∧ d i t ≤ 1)
    (h0 : arcCost d = 0)
    (hm : ∀ n : ℕ, 0 < n → structureFactor x n = -Complex.I * arcMode n d) :
    RepresentsDipole x 0 := by
  apply (representsDipole_iff_structureFactor x 0).2
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [structureFactor_zero]
  · rw [hm n hn, arcMode_eq_dipole_of_zero_cost d hi hd h0]
    have hu : unitPhase 0 = 1 := by simp [unitPhase]
    rcases Nat.even_or_odd n with he | ho
    · simp [hu, dipoleMode, he, he.neg_one_pow]
    · norm_num [hu, dipoleMode, Nat.not_even_iff_odd.mpr ho, ho.neg_one_pow, mul_comm (2:ℂ),
        ← mul_assoc, Complex.I_mul_I]

end GaussianChains
