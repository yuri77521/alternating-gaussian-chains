import BifurcationMinimizers

/-! Proposition 4 of the frozen paper. The first site is fixed at zero to
quotient translations, and `Feasible` checks all six gaps, including the wrap. -/
noncomputable section
namespace GaussianChains

open Bifurcation PackedFace Filter Asymptotics Set
open scoped Topology

/-- The constrained centered branch and its two bifurcating minima at width eight. -/
structure WidthEightPitchfork : Prop where
  centered {h : ℝ} : 0 < h → h ≤ hcEight →
    ∃ ε>0, ∀ x : Fin 6 → ℝ, dist x (sites h 0) < ε → x 0 = 0 →
      Feasible (by decide) h x → x ≠ sites h 0 → physicalEnergy 8 1 (sites h 0) < physicalEnergy 8 1 x
  saddle {h : ℝ} : hcEight < h → h < 1/6 → ∀ ε>0, ∃ x y : Fin 6 → ℝ,
    dist x (sites h 0) < ε ∧ dist y (sites h 0) < ε ∧ x 0 = 0 ∧ y 0 = 0 ∧
    Feasible (by decide) h x ∧ Feasible (by decide) h y ∧
    physicalEnergy 8 1 x < physicalEnergy 8 1 (sites h 0) ∧ physicalEnergy 8 1 (sites h 0) < physicalEnergy 8 1 y
  branches : ∃ t : ℝ → ℝ, Tendsto t (𝓝[>] 0) (𝓝 0) ∧
    ((fun δ => t δ - Real.sqrt (-6*mixedCritical/fourthCritical)*δ^(1/2:ℝ))
      =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
    ((fun δ => faceEnergy (hcEight+δ) 0 - faceEnergy (hcEight+δ) (t δ) -
      (3*mixedCritical^2/(2*fourthCritical))*δ^2)
        =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) ∧
    ((fun δ => -t δ - (-Real.sqrt (-6*mixedCritical/fourthCritical))*δ^(1/2:ℝ))
      =O[𝓝[>] 0] (fun δ : ℝ => δ^(3/2:ℝ))) ∧
    ((fun δ => faceEnergy (hcEight+δ) 0 - faceEnergy (hcEight+δ) (-t δ) -
      (3*mixedCritical^2/(2*fourthCritical))*δ^2)
        =O[𝓝[>] 0] (fun δ : ℝ => δ^3)) ∧
    ∃ r > (0:ℝ), ∀ᶠ δ in 𝓝[>] 0, 0 < t δ ∧ t δ < r ∧ t δ < bound (hcEight+δ) ∧
      (∀ v, minimizesEnergy 8 (hcEight+δ) v ↔ v = t δ ∨ v = -t δ) ∧
      ∀ v (u : Bifurcation.Release), |v| < r → ‖u‖ < r → (v,u) ∈ chartDomain (hcEight+δ) →
        (IsLocalMinOn (physicalEnergy 8 1)
            {x : Fin 6 → ℝ | x 0 = 0 ∧ Feasible (by decide) (hcEight+δ) x}
            (Release.sites (hcEight+δ) v u) ↔ u = 0 ∧ (v = t δ ∨ v = -t δ))
  threshold : (Images.lowerFloor:ℝ) < hcEight ∧ hcEight < (Images.upperFloor:ℝ)
  criticalDerivatives : (-58.94248 < mixedCritical ∧ mixedCritical < -58.94246) ∧
    (70.22242 < fourthCritical ∧ fourthCritical < 70.22244) ∧
    (0.40191212 < deriv (fun h => faceEnergy h 0) hcEight / 4 ∧
      deriv (fun h => faceEnergy h 0) hcEight / 4 < 0.40191214)
  coefficients : (2.24414 < Real.sqrt (-6*mixedCritical/fourthCritical) ∧
    Real.sqrt (-6*mixedCritical/fourthCritical) < 2.24416) ∧
    (74.2115 < 3*mixedCritical^2/(2*fourthCritical) ∧
      3*mixedCritical^2/(2*fourthCritical) < 74.2119)

theorem proposition4 : WidthEightPitchfork := by
  refine ⟨@centered_strict_physical,@centered_saddle_physical,?_,root_floor_bounds,critical_coefficients,pitch_coefficients⟩
  obtain ⟨t,ht,hd,hg,hdneg,hgneg,r,hr,Hu⟩ := width_eight_nearby_minimizers
  refine ⟨t,ht,hd,hg,hdneg,hgneg,r,hr,?_⟩
  filter_upwards [Hu] with δ H
  refine ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,?_⟩
  intro v u hv hu hp
  exact (chart_localMin_iff_physical hp).symm.trans (H.2.2.2.2 v u hv hu hp)

#print axioms proposition4

end GaussianChains
