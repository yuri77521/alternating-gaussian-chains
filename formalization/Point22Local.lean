import Point22Assembly
import Point22LocalShape

/-! Global classification conditional on exhaustive continuous-domain localization. -/
namespace GaussianChains.Point22
open Root22 Set

theorem global_shape_of_atlas
    (atlas : ∀ x : Fin 6 → ℝ, IsGroundState (by decide) (1/1000) 22 x → LocalizedAt x (1/1000)) :
    ∃ R : ℝ, (lowerRoot:ℝ) < R ∧ R < (upperRoot:ℝ) ∧
      (∀ x : Fin 6 → ℝ, IsGroundState (by decide) (1/1000) 22 x ↔
        ∃ k : Fin 6, gap (by decide) x = rotate (gapWord (1/1000) R) k) ∧
      minimumEnergy (N:=6) (by decide) (1/1000) 22 = imageEnergy 22 (sites (1/1000) R) := by
  obtain ⟨R,hl,hu,hs⟩ := unique_captured_minimum
  have hR : 2*(1/1000:ℝ) < R := lt_trans (by norm_num [lowerRoot]) hl
  have hR' : R < 1/2-(1/1000:ℝ) := lt_trans hu (by norm_num [upperRoot])
  exact ⟨R,hl,hu,classification_of_localization hR hR' atlas hs⟩

#print axioms global_shape_of_atlas

end GaussianChains.Point22


