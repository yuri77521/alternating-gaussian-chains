import Point22Local
import CertRootValue

/-! Physical consequences of complete localization, including the printed
energy interval and the two charge-preserving orbits. -/

namespace GaussianChains.Point22
open Root22

noncomputable abbrev paperFloor : ℝ := 1/1000

theorem root_cell_agrees (R : ℝ) : reflectedSites R = sites paperFloor R := by
  funext i
  fin_cases i <;> norm_num [reflectedSites,sites,paperFloor]

/-- All conclusions of the isolated-point theorem from exact localization.
The separate atlas acceptance theorem is needed to discharge the hypothesis. -/
theorem printed_point_of_capture
    (atlas : ∀ x : Fin 6 → ℝ, IsGroundState (by decide) paperFloor 22 x → LocalizedAt x paperFloor) :
    ∃ R : ℝ, (lowerRoot:ℝ) < R ∧ R < (upperRoot:ℝ) ∧
      (∀ x : Fin 6 → ℝ, IsGroundState (by decide) paperFloor 22 x ↔
        ∃ k : Fin 6, gap (by decide) x = rotate (gapWord paperFloor R) k) ∧
      minimumEnergy (N:=6) (by decide) paperFloor 22 = physicalEnergy 22 1 (sites paperFloor R) ∧
      (energyLower:ℝ) < minimumEnergy (N:=6) (by decide) paperFloor 22 ∧
      minimumEnergy (N:=6) (by decide) paperFloor 22 < (energyUpper:ℝ) ∧
      ∀ k l : Fin 6,
        SameSpeciesCells (shiftLifts (by decide) (sites paperFloor R) k)
          (shiftLifts (by decide) (sites paperFloor R) l) ↔ k.val%2 = l.val%2 := by
  obtain ⟨R,hl,hu,hg,hm⟩ := global_shape_of_atlas atlas
  have hE := reflection_energy_enclosed (r:=R) ⟨hl.le,hu.le⟩
  rw [root_cell_agrees] at hE
  have hR : 2*paperFloor < R := lt_trans (by norm_num [lowerRoot,paperFloor]) hl
  have hR' : R < 1/2-paperFloor := lt_trans hu (by norm_num [upperRoot,paperFloor])
  have hphys : physicalEnergy 22 1 (sites paperFloor R) = imageEnergy 22 (sites paperFloor R) := by
    simpa using physicalEnergy_eq_imageEnergy (N:=6) (by decide) 22 1 (by norm_num) (by norm_num)
      (sites paperFloor R)
  exact ⟨R,hl,hu,hg,hm.trans hphys.symm,hE.1.trans_eq hm.symm,hm.trans_lt hE.2,
    two_species_orbits paperFloor R hR hR'⟩

end GaussianChains.Point22
