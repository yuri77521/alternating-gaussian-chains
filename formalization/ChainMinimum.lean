import ChainCompact
import KernelFourier
import Mathlib.Topology.Order.Compact

/-! The attained minimum over the full labelled feasible cell, including
the collision closure at floor zero. Translation is fixed only in the proof. -/
namespace GaussianChains

def IsGroundState {N : ℕ} (hN : 0 < N) (h s : ℝ) (x : Fin N → ℝ) : Prop :=
  Feasible hN h x ∧ ∀ y, Feasible hN h y → imageEnergy s x ≤ imageEnergy s y

noncomputable def minimumEnergy {N : ℕ} (hN : 0 < N) (h s : ℝ) : ℝ :=
  sInf (imageEnergy s '' {x | Feasible hN h x})

theorem imageEnergy_sub_const {N : ℕ} (s : ℝ) (x : Fin N → ℝ) (a : ℝ) :
    imageEnergy s (fun i => x i - a) = imageEnergy s x := by
  simp only [imageEnergy, sub_sub_sub_cancel_right]

theorem imageEnergy_sitesOfGaps_gap {N : ℕ} (hN : 0 < N) (s : ℝ) (x : Fin N → ℝ) :
    imageEnergy s (sitesOfGaps (gap hN x)) = imageEnergy s x := by
  rw [show sitesOfGaps (gap hN x) = fun i => x i - x ⟨0, hN⟩ from
    funext (sitesOfGaps_gap hN x), imageEnergy_sub_const]

/-- A minimizer check on the full gap simplex covers every translated labelled cell. -/
theorem groundState_iff_gap_min {N : ℕ} (hN : 0 < N) (h s : ℝ) (x : Fin N → ℝ) :
    IsGroundState hN h s x ↔ gap hN x ∈ gapSimplex N h ∧
      IsMinOn (fun g => imageEnergy s (sitesOfGaps g)) (gapSimplex N h) (gap hN x) := by
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨⟨hx, sum_gap hN x⟩, isMinOn_iff.mpr ?_⟩
    intro g hg
    rw [imageEnergy_sitesOfGaps_gap]
    apply hm
    intro i
    rw [gap_sitesOfGaps hN g hg.2 i]
    exact hg.1 i
  · rintro ⟨hx, hm⟩
    refine ⟨hx.1, fun y hy => ?_⟩
    simpa only [imageEnergy_sitesOfGaps_gap] using
      isMinOn_iff.mp hm (gap hN y) ⟨hy, sum_gap hN y⟩

theorem exists_groundState {N : ℕ} (hN : 0 < N) {h s : ℝ}
    (h₀ : 0 ≤ h) (h₁ : h ≤ 1 / (N : ℝ)) (hs : 0 < s) :
    ∃ x, IsGroundState hN h s x := by
  obtain ⟨g, hg, hm⟩ := (isCompact_gapSimplex N h₀).exists_isMinOn
    (gapSimplex_nonempty hN h₁)
    ((continuous_imageEnergy hs).comp (continuous_sitesOfGaps N)).continuousOn
  refine ⟨sitesOfGaps g, ?_, ?_⟩
  · intro i
    rw [gap_sitesOfGaps hN g hg.2 i]
    exact hg.1 i
  · intro y hy
    have h := isMinOn_iff.mp hm (gap hN y) ⟨hy, sum_gap hN y⟩
    change imageEnergy s (sitesOfGaps g) ≤ imageEnergy s (sitesOfGaps (gap hN y)) at h
    rwa [imageEnergy_sitesOfGaps_gap] at h

theorem groundState_energy_eq_minimum {N : ℕ} {hN : 0 < N} {h s : ℝ}
    {x : Fin N → ℝ} (hx : IsGroundState hN h s x) :
    imageEnergy s x = minimumEnergy hN h s := by
  have hl : IsLeast (imageEnergy s '' {y | Feasible hN h y}) (imageEnergy s x) := by
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hx.2 y hy
  exact hl.csInf_eq.symm

theorem exists_minimumEnergy {N : ℕ} (hN : 0 < N) {h s : ℝ}
    (h₀ : 0 ≤ h) (h₁ : h ≤ 1 / (N : ℝ)) (hs : 0 < s) :
    ∃ x, Feasible hN h x ∧ imageEnergy s x = minimumEnergy hN h s := by
  obtain ⟨x, hx⟩ := exists_groundState hN h₀ h₁ hs
  exact ⟨x, hx.1, groundState_energy_eq_minimum hx⟩

end GaussianChains
