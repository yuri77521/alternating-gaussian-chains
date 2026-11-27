import ChainMinimum

/-! Global optimization in physical units. Both directions quantify over
every labelled competitor with the same period and physical gap floor. -/
namespace GaussianChains

def IsPhysicalGroundState {N : ℕ} (hN : 0 < N) (α L floor : ℝ) (X : Fin N → ℝ) : Prop :=
  (∀ i, floor ≤ physicalGap hN L X i) ∧
    ∀ Y, (∀ i, floor ≤ physicalGap hN L Y i) → physicalEnergy α L X ≤ physicalEnergy α L Y

/-- Passing between physical and period-normalized units preserves the full
set of minimizers. This also applies at zero gap, where label collisions are allowed. -/
theorem physical_groundState_iff {N : ℕ} (hN : 0 < N) {α L : ℝ}
    (hα : 0 < α) (hL : 0 < L) (floor : ℝ) (X : Fin N → ℝ) :
    IsPhysicalGroundState hN α L floor X ↔
      IsGroundState hN (floor/L) (α*L^2) (fun i => X i/L) := by
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨(physicalFeasible_iff hN hL floor X).mp hx, ?_⟩
    intro y hy
    let Y (i : Fin N) := y i * L
    have hY : (fun i => Y i/L) = y := by funext i; simp [Y, hL.ne']
    have hf := (physicalFeasible_iff hN hL floor Y).mpr (hY.symm ▸ hy)
    have he := hm Y hf
    rwa [physicalEnergy_eq_imageEnergy hN α L hα hL X,
      physicalEnergy_eq_imageEnergy hN α L hα hL Y, hY] at he
  · rintro ⟨hx, hm⟩
    refine ⟨(physicalFeasible_iff hN hL floor X).mpr hx, ?_⟩
    intro Y hy
    rw [physicalEnergy_eq_imageEnergy hN α L hα hL X,
      physicalEnergy_eq_imageEnergy hN α L hα hL Y]
    exact hm _ ((physicalFeasible_iff hN hL floor Y).mp hy)

/-- The infimum of the original directed energies equals the normalized
minimum value wherever the feasible simplex is nonempty. The image sets
actually agree even without this restriction. -/
theorem physical_infimum_eq_minimumEnergy {N : ℕ} (hN : 0 < N) {α L : ℝ}
    (hα : 0 < α) (hL : 0 < L) (floor : ℝ) :
    sInf (physicalEnergy α L '' {X | ∀ i, floor ≤ physicalGap hN L X i}) =
      minimumEnergy hN (floor/L) (α*L^2) := by
  unfold minimumEnergy
  apply congrArg sInf
  ext e
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨_, (physicalFeasible_iff hN hL floor X).mp hX,
      (physicalEnergy_eq_imageEnergy hN α L hα hL X).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let X (i : Fin N) := x i * L
    have hX : (fun i => X i/L) = x := by funext i; simp [X, hL.ne']
    refine ⟨X, (physicalFeasible_iff hN hL floor X).mpr (hX.symm ▸ hx), ?_⟩
    rw [physicalEnergy_eq_imageEnergy hN α L hα hL X, hX]

#print axioms physical_groundState_iff
#print axioms physical_infimum_eq_minimumEnergy

end GaussianChains
