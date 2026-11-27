import ClusterSeriesOrbits
import ClusterSeriesCandidate

namespace GaussianChains.ClusterSeries

open OddBlock

/-- The two marked gaps of the canonical antipodal coordinates are the wrap
at label -1 and the gap after the positive-net-charge block at label 2k. -/
theorem packedSites_marked (k l : ℕ) (h : ℝ) (i : ℤ) :
    gapAtInt (by omega) (packedSites k l h) i =
      markedGap h (1/2 - ((k:ℝ)+l)*h) (2*(k:ℤ)+1 + (2*(l:ℤ)+1)) (2*k+1) (-1) i := by
  let N : ℕ := (2*k+1)+(2*l+1)
  have hN : 0 < (N:ℤ) := by dsimp [N]; positivity
  have hNcast : (N:ℤ) = 2*(k:ℤ)+1+(2*(l:ℤ)+1) := rfl
  rw [← hNcast]
  unfold gapAtInt
  rw [packedSites_gap]
  let j := cellIndex (by dsimp [N]; omega : 0<N) i
  have hrep : (j.val:ℤ) = i % (N:ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')
  have hlast : i ≡ -1 [ZMOD (N:ℤ)] ↔ j.val+1=N := by
    change i % (N:ℤ) = (-1) % (N:ℤ) ↔ _
    have hneg := (Int.add_modEq_right (n := (N:ℤ)) (a := -1)).eq.symm
    have ht : (-1+(N:ℤ))%(N:ℤ) = -1+(N:ℤ) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hneg, ht, ← hrep]
    omega
  have hmiddle : i ≡ -1+(2*(k:ℤ)+1) [ZMOD (N:ℤ)] ↔ j.val=2*k := by
    change i % (N:ℤ) = _ % _ ↔ _
    have ht : (2*(k:ℤ))%(N:ℤ)=2*k :=
      Int.emod_eq_of_lt (by positivity) (by rw [hNcast]; omega)
    rw [show -1+(2*(k:ℤ)+1)=2*k by ring, ht, ← hrep]
    omega
  unfold markedGap
  change (if j.val=2*k ∨ j.val+1=N then _ else _) = _
  simp only [hlast, hmiddle, or_comm]

/-- The full species-preserving isometry relation on recuts of the packed
real coordinates. In particular recuts 0 and 1 represent different orbits
for unequal blocks, and every recut belongs to one of those two orbits. -/
theorem packed_sites_orbits_iff (k l : ℕ) {h : ℝ}
    (hh : h < 1 / (((2*k+1)+(2*l+1):ℕ):ℝ)) (t u : ℤ) :
    let X := integerSite (by omega) (packedSites k l h)
    SameSpeciesSites (fun i => X (i+t)) (fun i => X (i+u)) ↔ t%2=u%2 ∨ k=l := by
  let X := integerSite (by omega) (packedSites k l h)
  have hwidth : h ≠ 1/2 - ((k:ℝ)+l)*h := by
    have hp : 0 < (((2*k+1)+(2*l+1):ℕ):ℝ) := by positivity
    have ht := (lt_div_iff₀ hp).mp hh
    push_cast at ht
    intro he
    nlinarith
  have hpar : (2:ℤ) ∣ 2*(k:ℤ)+1 + (2*(l:ℤ)+1) := ⟨k+l+1, by ring⟩
  have hx (i : ℤ) : X (i+1)-X i =
      markedGap h (1/2 - ((k:ℝ)+l)*h) (2*(k:ℤ)+1 + (2*(l:ℤ)+1)) (2*k+1) (-1) i :=
    (integerSite_step _ _ _).trans (packedSites_marked k l h i)
  change SameSpeciesSites (fun i => X (i+t)) (fun i => X (i+u)) ↔ _
  rw [sameSpecies_recut_iff hwidth hpar (by omega) (by omega) (by omega) X hx]
  omega

theorem equal_blocks_one_orbit (k : ℕ) {h : ℝ}
    (hh : h < 1/(((2*k+1)+(2*k+1):ℕ):ℝ)) (t u : ℤ) :
    let X := integerSite (by omega) (packedSites k k h)
    SameSpeciesSites (fun i => X (i+t)) (fun i => X (i+u)) :=
  (packed_sites_orbits_iff k k hh t u).mpr (Or.inr rfl)

theorem unequal_blocks_two_orbits {k l : ℕ} (hkl : k ≠ l) {h : ℝ}
    (hh : h < 1/(((2*k+1)+(2*l+1):ℕ):ℝ)) :
    let X := integerSite (by omega) (packedSites k l h)
    let recut := fun (t i : ℤ) => X (i+t)
    ¬SameSpeciesSites (recut 0) (recut 1) ∧
    ∀ t, SameSpeciesSites (recut 0) (recut t) ∨ SameSpeciesSites (recut 1) (recut t) := by
  dsimp only
  constructor
  · intro he
    have := (packed_sites_orbits_iff k l hh 0 1).mp he
    omega
  · intro t
    rcases (show t%2=0 ∨ t%2=1 by omega) with ht | ht
    · exact Or.inl ((packed_sites_orbits_iff k l hh 0 t).mpr (Or.inl (by omega)))
    · exact Or.inr ((packed_sites_orbits_iff k l hh 1 t).mpr (Or.inl (by omega)))

#print axioms packed_sites_orbits_iff

end GaussianChains.ClusterSeries
