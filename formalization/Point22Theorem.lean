import Point22FromAtlas
import Point22Consequences
import Point22TwoTreesComplete
import CertRootSimple

/-! The full isolated-point classification on the original ordered six-site
feasible set. No localization or certificate-acceptance hypothesis is exported. -/

namespace GaussianChains.Point22

theorem atlas_captures_all_ground_states (x : Fin 6 → ℝ)
    (hx : IsGroundState (by decide) paperFloor 22 x) : LocalizedAt x paperFloor :=
  Atlas.physical_localize_two_trees_checked x hx

/-- Theorem 6 of the frozen paper. The energy uses the normalized physical
period L=1, and the infimum ranges over every feasible six-label cell. -/
theorem theorem6 :
    ∃ R : ℝ, 0.249999032167246504146498709394 < R ∧ R < 0.249999032167246504146498709395 ∧
      (∀ x : Fin 6 → ℝ, IsGroundState (by decide) (1/1000) 22 x ↔
        ∃ k : Fin 6, gap (by decide) x = rotate (gapWord (1/1000) R) k) ∧
      minimumEnergy (N:=6) (by decide) (1/1000) 22 = physicalEnergy 22 1 (sites (1/1000) R) ∧
      0.66503584451339086827047430 < minimumEnergy (N:=6) (by decide) (1/1000) 22 ∧
      minimumEnergy (N:=6) (by decide) (1/1000) 22 < 0.66503584451339086827047431 ∧
      ∀ k l : Fin 6,
        SameSpeciesCells (shiftLifts (by decide) (sites (1/1000) R) k)
          (shiftLifts (by decide) (sites (1/1000) R) l) ↔ k.val%2 = l.val%2 := by
  convert printed_point_of_capture atlas_captures_all_ground_states using 1 <;>
    norm_num [Root22.lowerRoot, Root22.upperRoot, Root22.energyLower, Root22.energyUpper,paperFloor]

#print axioms theorem6

/-- The root in the force enclosure is the same R that gives every physical
minimum. The derivative and the quantification over all roots identify it
within the complete certified local interval. -/
theorem unique_root_gives_all_ground_states :
    ∃ R : ℝ, (Root22.lowerRoot:ℝ) < R ∧ R < (Root22.upperRoot:ℝ) ∧
      Root22.paperForce R = 0 ∧ 14 < deriv Root22.paperForce R ∧
      (∀ y ∈ Set.Icc (21/100:ℝ) (29/100), Root22.paperForce y = 0 → y = R) ∧
      ∀ x : Fin 6 → ℝ, IsGroundState (by decide) paperFloor 22 x ↔
        ∃ k : Fin 6, gap (by decide) x = rotate (gapWord paperFloor R) k := by
  obtain ⟨R,hl,hu,hF,hd,unique⟩ := Root22.paper_force_unique_simple
  have h₁ : 2*paperFloor < R := lt_trans (by norm_num [Root22.lowerRoot,paperFloor]) hl
  have h₂ : R < 1/2-paperFloor := lt_trans hu (by norm_num [Root22.upperRoot,paperFloor])
  have hs := classification_of_localization h₁ h₂ atlas_captures_all_ground_states
    (fun _ => strict_local_shape hl hu hF)
  exact ⟨R,hl,hu,hF,hd,unique,hs.1⟩

theorem witnessX_minus_global_minimum :
    0.00207096589396576 <
      imageEnergy 22 (fun i => (Root22.witnessX i : ℝ)) -
        minimumEnergy (N:=6) (by decide) (1/1000) 22 := by
  obtain ⟨_,_,_,_,_,_,hu,_⟩ := theorem6
  linarith [Root22.witnessX_enclosed.1]

end GaussianChains.Point22
