import ChainGeometry
import ChainEnergy
import ClustersOrbits

namespace GaussianChains.ClusterSeries

open OddBlock

/-- The label in a single cell representing an arbitrary integer index. -/
def cellIndex {N : ℕ} (hN : 0 < N) (i : ℤ) : Fin N :=
  ⟨(i % (N : ℤ)).toNat, by
    have h₀ := Int.emod_nonneg i (by exact_mod_cast hN.ne' : (N:ℤ) ≠ 0)
    have h₁ := Int.emod_lt_of_pos i (by exact_mod_cast hN : 0 < (N:ℤ))
    omega⟩

theorem charge_cellIndex {N : ℕ} (hN : 0<N) (he : (2:ℤ) ∣ (N:ℤ)) (i : ℤ) :
    charge (cellIndex hN i) = (-1 : ℝ) ^ ((i%2).toNat) := by
  unfold charge
  rw [neg_one_pow_eq_pow_mod_two]
  congr 1
  have hr : ((cellIndex hN i).val:ℤ) = i%(N:ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne' : (N:ℤ) ≠ 0))
  have hm := (Int.mod_modEq i (N:ℤ)).of_dvd he
  change (i%(N:ℤ))%2=i%2 at hm
  have ht : (0:ℤ) ≤ i%2 := Int.emod_nonneg _ (by decide)
  omega

/-- Both index transformations in the real-space isometry relation preserve
the physical charge on every label. -/
theorem isometry_charge {N : ℕ} (hN : 0<N) (he : (2:ℤ) ∣ (N:ℤ)) (d i : ℤ) :
    charge (cellIndex hN (i+2*d)) = charge (cellIndex hN i) ∧
    charge (cellIndex hN (2*d-i)) = charge (cellIndex hN i) := by
  simp only [charge_cellIndex hN he]
  rw [show (i+2*d)%2=i%2 by omega, show (2*d-i)%2=i%2 by omega]
  exact ⟨rfl,rfl⟩

theorem recut_one_charge {N : ℕ} (hN : 0<N) (he : (2:ℤ) ∣ (N:ℤ)) (i : ℤ) :
    charge (cellIndex hN (i+1)) = -charge (cellIndex hN i) := by
  simp only [charge_cellIndex hN he]
  rcases (show i%2=0 ∨ i%2=1 by omega) with hi | hi
  · simp [hi, show (i+1)%2=1 by omega]
  · simp [hi, show (i+1)%2=0 by omega]

noncomputable def gapAtInt {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : ℤ) : ℝ :=
  gap hN x (cellIndex hN i)

/-- Coordinates along the full alternating chain. For a negative index the
backwards sum subtracts precisely the intervening gaps before label zero. -/
noncomputable def integerSite {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) : ℤ → ℝ
  | .ofNat j => liftSite hN x j
  | .negSucc j => x ⟨0,hN⟩ - ∑ t ∈ Finset.range (j+1), gapAtInt hN x (.negSucc t)

theorem integerSite_fin {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N) :
    integerSite hN x (i.val:ℤ) = x i := liftSite_fin hN x i

theorem integerSite_step {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : ℤ) :
    integerSite hN x (i+1) - integerSite hN x i = gapAtInt hN x i := by
  cases i with
  | ofNat j =>
    change liftSite hN x (j+1) - liftSite hN x j = _
    rw [gap_lift_period]
    unfold gapAtInt cellIndex
    congr 1
  | negSucc j =>
    cases j with
    | zero =>
      change liftSite hN x 0 - (x ⟨0,hN⟩ - _) = _
      rw [(liftSite_fin hN x ⟨0,hN⟩ : liftSite hN x 0 = _)]
      simp
    | succ j =>
      change (x ⟨0,hN⟩ - ∑ t ∈ Finset.range (j+1), gapAtInt hN x (.negSucc t)) -
        (x ⟨0,hN⟩ - ∑ t ∈ Finset.range (j+1+1), gapAtInt hN x (.negSucc t)) = _
      rw [Finset.sum_range_succ _ (j+1)]
      ring

private theorem eq_zeroValue_of_step (f : ℤ → ℝ) (hf : ∀ i, f (i+1) = f i) (i : ℤ) :
    f i = f 0 := by
  refine Int.inductionOn' i 0 rfl (fun k _ ih => (hf k).trans ih) ?_
  intro k _ ih
  exact (show f (k-1)=f k by simpa using (hf (k-1)).symm).trans ih

theorem integerSite_add_period {N : ℕ} (hN : 0<N) (x : Fin N → ℝ) (i : ℤ) :
    integerSite hN x (i+N) = integerSite hN x i + 1 := by
  let f (j : ℤ) := integerSite hN x (j+N) - integerSite hN x j
  have hf (j : ℤ) : f (j+1)=f j := by
    have hindex : cellIndex hN (j+N) = cellIndex hN j :=
      Fin.ext (congrArg Int.toNat (Int.add_modEq_right (a := j) (n := (N:ℤ))).eq)
    have hgap : gapAtInt hN x (j+N) = gapAtInt hN x j :=
      congrArg (gap hN x) hindex
    dsimp [f]
    rw [show j+1+N=j+N+1 by ring]
    linarith [integerSite_step hN x (j+N), integerSite_step hN x j]
  have h₀ : f 0 = 1 := by
    dsimp only [f]
    rw [zero_add]
    change liftSite hN x N - liftSite hN x 0 = 1
    simpa using (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using liftSite_add_period hN x 0) :
      liftSite hN x N - liftSite hN x 0 = 1)
  have hi := (eq_zeroValue_of_step f hf i).trans h₀
  dsimp [f] at hi
  linarith

/-- Translations and reflections of the lifted sites, with even changes of
the label origin in both orientations. -/
def SameSpeciesSites (X Y : ℤ → ℝ) : Prop :=
  ∃ d : ℤ, ∃ T : ℝ,
    (∀ i, Y (i+2*d) = X i + T) ∨ (∀ i, Y (2*d-i) = T-X i)

theorem sameSpeciesSites_iff_steps (X Y : ℤ → ℝ) :
    SameSpeciesSites X Y ↔ ∃ d : ℤ,
      (∀ i, X (i+1)-X i = Y ((i+2*d)+1) - Y (i+2*d)) ∨
      (∀ i, X (i+1)-X i = Y ((2*d-1-i)+1) - Y (2*d-1-i)) := by
  constructor
  · rintro ⟨d,T,h | h⟩
    · refine ⟨d, Or.inl (fun i => ?_)⟩
      rw [show i+2*d+1=i+1+2*d by ring, h, h]
      ring
    · refine ⟨d, Or.inr (fun i => ?_)⟩
      rw [show 2*d-1-i+1=2*d-i by ring, show 2*d-1-i=2*d-(i+1) by ring, h, h]
      ring
  · rintro ⟨d,h | h⟩
    · let f (i : ℤ) := Y (i+2*d) - X i
      have hf (i : ℤ) : f (i+1)=f i := by
        dsimp [f]
        rw [show i+1+2*d=i+2*d+1 by ring]
        linarith [h i]
      refine ⟨d,f 0,Or.inl (fun i => ?_)⟩
      have heq := eq_zeroValue_of_step f hf i
      change Y (i+2*d) - X i = f 0 at heq
      linarith
    · let f (i : ℤ) := Y (2*d-i) + X i
      have hf (i : ℤ) : f (i+1)=f i := by
        have heq := h i
        rw [show 2*d-1-i+1=2*d-i by ring, show 2*d-1-i=2*d-(i+1) by ring] at heq
        dsimp [f]
        linarith
      refine ⟨d,f 0,Or.inr (fun i => ?_)⟩
      have heq := eq_zeroValue_of_step f hf i
      change Y (2*d-i) + X i = f 0 at heq
      linarith

/-- For two configurations with the locked gap pattern, the only
possible real-space species-preserving isometries identify precisely the two
parity classes of the marked gap, merging them when the blocks are equal. -/
theorem sameSpecies_locked_lifts_iff {N r a b : ℤ} {h H : ℝ}
    (hwidth : h ≠ H) (he : 2 ∣ N) (hr : 0<r) (hrN : r<N) (hodd : r%2=1)
    (X Y : ℤ → ℝ)
    (hx : ∀ i, X (i+1) - X i = markedGap h H N r a i)
    (hy : ∀ i, Y (i+1) - Y i = markedGap h H N r b i) :
    SameSpeciesSites X Y ↔ a%2=b%2 ∨ 2*r=N := by
  rw [sameSpeciesSites_iff_steps]
  simp_rw [hx, hy]
  rw [← speciesEquivMarkers_iff_gap hwidth hr hrN, speciesEquivMarkers_iff he hr hrN hodd]

theorem sameSpecies_locked_sites_iff {N : ℕ} (hN : 0<N) {r a b : ℤ} {h H : ℝ}
    (hwidth : h ≠ H) (he : (2:ℤ) ∣ (N:ℤ)) (hr : 0<r) (hrN : r<(N:ℤ)) (hodd : r%2=1)
    (x y : Fin N → ℝ)
    (hx : ∀ i, gapAtInt hN x i = markedGap h H N r a i)
    (hy : ∀ i, gapAtInt hN y i = markedGap h H N r b i) :
    SameSpeciesSites (integerSite hN x) (integerSite hN y) ↔ a%2=b%2 ∨ 2*r=N :=
  sameSpecies_locked_lifts_iff hwidth he hr hrN hodd _ _
    (fun i => (integerSite_step hN x i).trans (hx i))
    (fun i => (integerSite_step hN y i).trans (hy i))

/-- One recut swaps all signs. Among recuts of a locked pattern it generates
the second orbit exactly when the two block sizes are unequal. -/
theorem sameSpecies_recut_iff {N r a : ℤ} {h H : ℝ} (hwidth : h ≠ H)
    (he : 2 ∣ N) (hr : 0<r) (hrN : r<N) (hodd : r%2=1) (X : ℤ → ℝ)
    (hx : ∀ i, X (i+1)-X i = markedGap h H N r a i) (t u : ℤ) :
    SameSpeciesSites (fun i => X (i+t)) (fun i => X (i+u)) ↔ t%2=u%2 ∨ 2*r=N := by
  have hshift (v i : ℤ) :
      X (i+1+v)-X (i+v) = markedGap h H N r (a-v) i := by
    rw [show i+1+v=i+v+1 by ring, hx]
    have trans (w : ℤ) : (i+v ≡ w [ZMOD N]) ↔ (i ≡ w-v [ZMOD N]) := by
      constructor
      · intro hv
        simpa using hv.sub_right v
      · intro hv
        simpa using hv.add_right v
    unfold markedGap
    simp only [trans, show a+r-v=a-v+r by ring]
  rw [sameSpecies_locked_lifts_iff hwidth he hr hrN hodd _ _ (hshift t) (hshift u)]
  omega

end GaussianChains.ClusterSeries
