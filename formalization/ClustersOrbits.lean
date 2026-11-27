import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-! The dihedral action on the two exceptional gaps of a packed configuration.
An orientation-preserving charge-preserving relabeling sends site `i` to
`i+2d`; the reflection sends it to `2d-i`. Its outgoing gap therefore goes
to gap `2d-i-1`. This distinction matters for unequal cluster sizes. -/

namespace GaussianChains.OddBlock

/-- Equality of unordered pairs of marked gap labels modulo the particle count. -/
def SameMarkers (N u v x y : ℤ) : Prop :=
  (u ≡ x [ZMOD N] ∧ v ≡ y [ZMOD N]) ∨ (u ≡ y [ZMOD N] ∧ v ≡ x [ZMOD N])

/-- Equivalence of two marked gap patterns under the species-preserving
dihedral action. Their large gaps are at a separation of `r` labels. -/
def SpeciesEquivMarkers (N r a b : ℤ) : Prop :=
  ∃ d : ℤ, SameMarkers N (a+2*d) (a+r+2*d) b (b+r) ∨
    SameMarkers N (2*d-1-a) (2*d-1-(a+r)) b (b+r)

private theorem opposite_modEq {N r : ℤ} (hr₀ : 0 < r) (hrN : r < N)
    (hr : r ≡ -r [ZMOD N]) : 2*r=N := by
  have h := hr.trans (Int.add_modEq_right (n := N) (a := -r)).symm
  change r % N = (-r+N) % N at h
  rw [Int.emod_eq_of_lt hr₀.le hrN, Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

/-- Both rotations and reflections. There is one orbit of labelled gap
patterns for equal counts, and two parity orbits for distinct odd counts. -/
theorem speciesEquivMarkers_iff {N r : ℤ} (he : 2 ∣ N) (hr₀ : 0 < r)
    (hrN : r < N) (hr₂ : r % 2 = 1) (a b : ℤ) :
    SpeciesEquivMarkers N r a b ↔ a%2 = b%2 ∨ 2*r=N := by
  constructor
  · rintro ⟨d, (⟨h, _⟩ | ⟨h,h'⟩) | (⟨h,h'⟩ | ⟨h, _⟩)⟩
    · left
      have hp := (h.of_dvd he).eq
      omega
    · right
      apply opposite_modEq hr₀ hrN
      convert h'.sub h using 1 <;> ring
    · right
      apply opposite_modEq hr₀ hrN
      convert h.sub h' using 1 <;> ring
    · left
      have hp := (h.of_dvd he).eq
      omega
  · rintro (hab | hN)
    · let d := (b-a)/2
      have hd : a+2*d=b := by dsimp only [d]; omega
      refine ⟨d, Or.inl (Or.inl ⟨hd ▸ Int.ModEq.rfl, ?_⟩)⟩
      rw [show a+r+2*d=b+r by omega]
    · by_cases hab : a%2=b%2
      · let d := (b-a)/2
        have hd : a+2*d=b := by dsimp only [d]; omega
        refine ⟨d, Or.inl (Or.inl ⟨hd ▸ Int.ModEq.rfl, ?_⟩)⟩
        rw [show a+r+2*d=b+r by omega]
      · let d := (b+r-a)/2
        have hd : a+2*d=b+r := by dsimp only [d]; omega
        refine ⟨d, Or.inl (Or.inr ⟨hd ▸ Int.ModEq.rfl, ?_⟩)⟩
        rw [show a+r+2*d=b+N by omega]
        exact Int.add_modEq_right

theorem reversed_species_equivalent_iff {k l : ℕ} (a : ℤ) :
    SpeciesEquivMarkers (2*(k:ℤ)+1 + (2*(l:ℤ)+1)) (2*(k:ℤ)+1) a (a+1) ↔ k=l := by
  have he : (2 : ℤ) ∣ (2*(k:ℤ)+1 + (2*(l:ℤ)+1)) := ⟨k+l+1, by ring⟩
  rw [speciesEquivMarkers_iff he (by omega) (by omega) (by omega)]
  omega

/-- Every gap is short except the two designated periodic labels. -/
def markedGap {α : Type*} (h H : α) (N r a i : ℤ) : α :=
  if i ≡ a [ZMOD N] ∨ i ≡ a+r [ZMOD N] then H else h

private theorem marker_membership {N u v x y : ℤ} (hm : SameMarkers N u v x y)
    (i : ℤ) : (i ≡ u [ZMOD N] ∨ i ≡ v [ZMOD N]) ↔
      (i ≡ x [ZMOD N] ∨ i ≡ y [ZMOD N]) := by
  rcases hm with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨Or.imp (fun h => h.trans h₁) (fun h => h.trans h₂),
           Or.imp (fun h => h.trans h₁.symm) (fun h => h.trans h₂.symm)⟩
  · constructor
    · rintro (h | h)
      · exact Or.inr (h.trans h₁)
      · exact Or.inl (h.trans h₂)
    · rintro (h | h)
      · exact Or.inr (h.trans h₂.symm)
      · exact Or.inl (h.trans h₁.symm)

private theorem markers_of_distinct {N u v x y : ℤ} (hne : ¬u ≡ v [ZMOD N])
    (hu : u ≡ x [ZMOD N] ∨ u ≡ y [ZMOD N]) (hv : v ≡ x [ZMOD N] ∨ v ≡ y [ZMOD N]) :
    SameMarkers N u v x y := by
  rcases hu with hx | hy <;> rcases hv with hx' | hy'
  · exact False.elim (hne (hx.trans hx'.symm))
  · exact Or.inl ⟨hx,hy'⟩
  · exact Or.inr ⟨hy,hx'⟩
  · exact False.elim (hne (hy.trans hy'.symm))

/-- For distinct gap widths, matching the two exceptional labels is equivalent
to matching the entire periodic gap word under the same species-preserving
index transformations. -/
theorem speciesEquivMarkers_iff_gap {α : Type*} {h H : α} (hH : h ≠ H)
    {N r : ℤ} (hr₀ : 0 < r) (hrN : r < N) (a b : ℤ) :
    SpeciesEquivMarkers N r a b ↔
      ∃ d : ℤ, (∀ i, markedGap h H N r a i = markedGap h H N r b (i+2*d)) ∨
               (∀ i, markedGap h H N r a i = markedGap h H N r b (2*d-1-i)) := by
  have neM : ¬ a ≡ a+r [ZMOD N] := by
    intro heq
    have ht := (Int.ModEq.rfl (a := a) (n := N)).sub heq
    have : (0:ℤ) ≡ r [ZMOD N] := by
      convert ht.neg using 1 <;> ring
    change 0%N=r%N at this
    rw [Int.zero_emod, Int.emod_eq_of_lt hr₀.le hrN] at this
    omega
  have member (i : ℤ) (hc : markedGap h H N r b i = H) :
      i ≡ b [ZMOD N] ∨ i ≡ b+r [ZMOD N] := by
    unfold markedGap at hc
    split at hc <;> first | assumption | contradiction
  constructor
  · rintro ⟨d, hd | hd⟩
    · refine ⟨d, Or.inl (fun i => ?_)⟩
      have hp := marker_membership hd (i+2*d)
      have tr (x : ℤ) : (i+2*d ≡ x+2*d [ZMOD N]) ↔ i ≡ x [ZMOD N] :=
        ⟨Int.ModEq.add_right_cancel' _, fun e => e.add_right _⟩
      rw [tr, tr] at hp
      unfold markedGap
      simp only [hp]
    · refine ⟨d, Or.inr (fun i => ?_)⟩
      have hp := marker_membership hd (2*d-1-i)
      have trans (x : ℤ) : (2*d-1-i ≡ 2*d-1-x [ZMOD N]) ↔ (i ≡ x [ZMOD N]) := by
        constructor
        · intro e
          convert e.sub_left (2*d-1) using 1 <;> ring
        · exact fun e => e.sub_left _
      rw [trans, trans] at hp
      unfold markedGap
      simp only [hp]
  · rintro ⟨d, hd | hd⟩
    · refine ⟨d, Or.inl <| markers_of_distinct (fun e => neM (Int.ModEq.add_right_cancel' (2*d) e)) ?_ ?_⟩
      · apply member
        rw [← hd]
        simp [markedGap]
      · apply member
        rw [← hd]
        simp [markedGap]
    · have hne : ¬(2*d-1-a) ≡ (2*d-1-(a+r)) [ZMOD N] := by
        intro e
        apply neM
        convert e.sub_left (2*d-1) using 1 <;> ring
      refine ⟨d, Or.inr <| markers_of_distinct hne ?_ ?_⟩
      · apply member
        rw [← hd]
        simp [markedGap]
      · apply member
        rw [← hd]
        simp [markedGap]

end GaussianChains.OddBlock
