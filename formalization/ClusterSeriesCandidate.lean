import ClusterSeriesEnergy
import ClusterSeriesDipole
import ChainMinimum

namespace GaussianChains.ClusterSeries

open Real
open scoped Asymptotics
open Filter Topology

theorem packedSites_eq (k l : ℕ) (h : ℝ) (j : Fin ((2*k+1)+(2*l+1))) :
    packedSites k l h j = if j.val < 2*k+1 then ((j.val:ℝ)-k)*h
      else 1/2 + (((j.val-(2*k+1):ℕ):ℝ)-l)*h := by
  unfold packedSites packedAngle
  split <;> field_simp [Real.pi_ne_zero]

/-- Every interior contact and both exterior gaps, including the wrap. -/
theorem packedSites_gap (k l : ℕ) (h : ℝ) (j : Fin ((2*k+1)+(2*l+1))) :
    gap (by omega) (packedSites k l h) j =
      if j.val = 2*k ∨ j.val+1 = (2*k+1)+(2*l+1) then
        1/2 - ((k:ℝ)+l)*h else h := by
  by_cases hj : j.val+1 = (2*k+1)+(2*l+1)
  · rw [gap_wrap _ _ _ hj, if_pos (Or.inr hj), packedSites_eq, packedSites_eq]
    have hlast : j.val - (2*k+1) = 2*l := by omega
    simp only [if_pos (by omega : 0 < 2*k+1),
      if_neg (by omega : ¬j.val < 2*k+1), hlast]
    push_cast
    ring
  · have hi : j.val+1 < (2*k+1)+(2*l+1) := by omega
    rw [gap_interior _ _ _ hi, packedSites_eq, packedSites_eq]
    by_cases hm : j.val = 2*k
    · rw [if_pos (Or.inl hm : j.val=2*k ∨ j.val+1=(2*k+1)+(2*l+1))]
      simp only [hm,
        if_neg (lt_irrefl _), if_pos (by omega : 2*k < 2*k+1), Nat.sub_self]
      push_cast
      ring
    · rw [if_neg (not_or.mpr ⟨hm,hj⟩)]
      by_cases hl : j.val < 2*k+1
      · simp only [if_pos hl, if_pos (by omega : j.val+1 < 2*k+1)]
        push_cast
        ring
      · simp only [if_neg hl, if_neg (by omega : ¬j.val+1 < 2*k+1)]
        have step : j.val+1 - (2*k+1) = (j.val - (2*k+1)) + 1 := by omega
        rw [step]
        push_cast
        ring

theorem packedSites_feasible (k l : ℕ) (h : ℝ)
    (hh : h ≤ 1 / (((2*k+1)+(2*l+1):ℕ):ℝ)) :
    Feasible (by omega) h (packedSites k l h) := by
  intro j
  rw [packedSites_gap]
  split
  · have hp : (0:ℝ) < (((2*k+1)+(2*l+1):ℕ):ℝ) := by positivity
    have ht := (le_div_iff₀ hp).mp hh
    push_cast at ht
    linarith
  · exact le_rfl

/-- Eq. (7) for the actual normalized image energy at the canonical
coordinates. Parameterization by angle makes the expansion variable explicit. -/
theorem imageEnergy_packedSites_fourth (k l : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun η : ℝ => imageEnergy s (packedSites k l (η / (2*π))) -
      energyPoly k l ((2*k+1)+(2*l+1)) s η) =O[nhds 0] (fun η : ℝ => η^6) := by
  have hη (η : ℝ) : 2*π*(η / (2*π)) = η := by field_simp
  simp_rw [imageEnergy_packedSites k l hs, hη]
  exact packedEnergy_fourth_dipole k l _ hs

/-- An unconditional upper bound on the full minimum, over *all* feasible
placements. This needs only feasibility of the packed trial. -/
theorem minimumEnergy_le_packed (k l : ℕ) {s h : ℝ} (hs : 0 < s) (h₀ : 0 ≤ h)
    (h₁ : h ≤ 1 / (((2*k+1)+(2*l+1):ℕ):ℝ)) :
    minimumEnergy (by omega : 0 < (2*k+1)+(2*l+1)) h s ≤
      1 - 2 * sqrt (π/s)/(((2*k+1)+(2*l+1):ℕ):ℝ) *
        packedMass k l (exp (-(π^2)/s)) (2*π*h) := by
  obtain ⟨x, hx⟩ := exists_groundState (by omega : 0 < (2*k+1)+(2*l+1)) h₀ h₁ hs
  rw [← groundState_energy_eq_minimum hx, ← imageEnergy_packedSites k l hs h]
  exact hx.2 _ (packedSites_feasible k l h h₁)

/-- The exact minimum formula after the minimizer classification supplies
ground-state membership of this packed pair. -/
theorem minimumEnergy_eq_of_packed_groundState (k l : ℕ) {s h : ℝ} (hs : 0 < s)
    (hx : IsGroundState (by omega) h s (packedSites k l h)) :
    minimumEnergy (by omega : 0 < (2*k+1)+(2*l+1)) h s =
      1 - 2 * sqrt (π/s)/(((2*k+1)+(2*l+1):ℕ):ℝ) *
        packedMass k l (exp (-(π^2)/s)) (2*π*h) := by
  rw [← groundState_energy_eq_minimum hx, imageEnergy_packedSites k l hs h]

/-- Transfer of the candidate expansion to the minimum along positive floors
once the classified packed configuration is known to minimize for all
sufficiently small positive angular spacings. -/
theorem minimumEnergy_fourth_of_packed_groundState (k l : ℕ) {s : ℝ} (hs : 0 < s)
    (hmin : ∀ᶠ η : ℝ in 𝓝[>] 0, IsGroundState (by omega) (η/(2*π)) s
      (packedSites k l (η/(2*π)))) :
    (fun η : ℝ => minimumEnergy (by omega : 0 < (2*k+1)+(2*l+1)) (η/(2*π)) s -
      energyPoly k l ((2*k+1)+(2*l+1)) s η) =O[𝓝[>] 0] (fun η : ℝ => η^6) := by
  refine ((imageEnergy_packedSites_fourth k l hs).mono nhdsWithin_le_nhds).congr' ?_
    (Filter.EventuallyEq.rfl)
  exact hmin.mono fun η hx => congrArg (fun a => a - energyPoly k l _ s η)
    (groundState_energy_eq_minimum hx)

/-- In the six-site specialization the exact quadratic and quartic prefactors
are 8c/3 and −14c/9, respectively, in the angular spacing. -/
theorem energyPoly_six {s : ℝ} (η : ℝ) :
    energyPoly 1 1 6 s η = dipoleEnergy 6 s +
      (8 * sqrt (π/s)/3) * parityMoment Odd (exp (-(π^2)/s)) 2 * η^2 -
      (14 * sqrt (π/s)/9) * parityMoment Odd (exp (-(π^2)/s)) 4 * η^4 := by
  unfold energyPoly coeff
  norm_num
  ring

#print axioms imageEnergy_packedSites_fourth
#print axioms minimumEnergy_eq_of_packed_groundState
#print axioms minimumEnergy_fourth_of_packed_groundState

end GaussianChains.ClusterSeries

