import ChainMinimum
import ChainClosure

/-! The zero-floor infimum in the open ordered class. -/
namespace GaussianChains

/-- Closing up collisions leaves the infimum unchanged. The value on the
right is attained on the closure; its attainment in the open class is separate. -/
theorem strict_infimum_eq_minimum {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s) :
    sInf (imageEnergy s '' {x | StrictlyOrdered hN x}) = minimumEnergy hN 0 s := by
  let E := fun g : Fin N → ℝ => imageEnergy s (sitesOfGaps g)
  let S := imageEnergy s '' {x | StrictlyOrdered hN x}
  have hp : (0:ℝ) < 1 / (N:ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hN)
  obtain ⟨x, hx⟩ := exists_groundState hN (le_refl 0) hp.le hs
  rw [← groundState_energy_eq_minimum hx]
  have hl : IsGLB S (imageEnergy s x) := by
    constructor
    · rintro _ ⟨y, hy, rfl⟩
      exact hx.2 y (fun i => (hy i).le)
    · intro r hr
      have h' : ∀ g ∈ strictGapSimplex N, r ≤ E g := by
        intro g hg
        apply hr
        refine ⟨sitesOfGaps g, ?_, rfl⟩
        intro i
        rw [gap_sitesOfGaps hN g hg.2 i]
        exact hg.1 i
      have hc := (lowerBound_strict_iff_closed hN
        ((continuous_imageEnergy hs).comp (continuous_sitesOfGaps N)) r).1 h'
      have h := hc (gap hN x) ⟨hx.1, sum_gap hN x⟩
      simpa only [Function.comp_apply, imageEnergy_sitesOfGaps_gap] using h
  obtain ⟨y, hy⟩ := (feasible_exists_iff hN (1 / (N:ℝ))).2 le_rfl
  exact hl.csInf_eq ⟨imageEnergy s y, y, strict_of_feasible hp hy, rfl⟩

end GaussianChains
