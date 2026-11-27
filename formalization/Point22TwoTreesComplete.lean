import Point22TwoTrees
import Point22TwoTreeRanges
import Point22Consequences

/-! End-to-end localization with the two surviving block trees and their
kernel-checked continuous range enclosures. -/
namespace GaussianChains.Point22.Atlas

theorem physical_localize_two_trees_checked (x : Fin 6 → ℝ)
    (hx : IsGroundState (by decide) (1/1000) 22 x) : LocalizedAt x (1/1000) :=
  physical_localize_two_trees two_tree_ranges_valid x hx

/-- The full physical classification, reported independently of acceptance of
the other ten block trees. Their analytic exclusions are incorporated above. -/
theorem theorem6_two_trees :
    ∃ R : ℝ, (Root22.lowerRoot:ℝ) < R ∧ R < (Root22.upperRoot:ℝ) ∧
      (∀ x : Fin 6 → ℝ, IsGroundState (by decide) paperFloor 22 x ↔
        ∃ k : Fin 6, gap (by decide) x = rotate (gapWord paperFloor R) k) ∧
      minimumEnergy (N:=6) (by decide) paperFloor 22 = physicalEnergy 22 1 (sites paperFloor R) ∧
      (Root22.energyLower:ℝ) < minimumEnergy (N:=6) (by decide) paperFloor 22 ∧
      minimumEnergy (N:=6) (by decide) paperFloor 22 < (Root22.energyUpper:ℝ) ∧
      ∀ k l : Fin 6,
        SameSpeciesCells (shiftLifts (by decide) (sites paperFloor R) k)
          (shiftLifts (by decide) (sites paperFloor R) l) ↔ k.val%2 = l.val%2 :=
  printed_point_of_capture physical_localize_two_trees_checked

#print axioms physical_localize_two_trees_checked
#print axioms theorem6_two_trees
end GaussianChains.Point22.Atlas
