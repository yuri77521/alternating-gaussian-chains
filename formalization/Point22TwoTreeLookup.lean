import Point22AtlasAcceptance

/-! Range-table restriction for the two surviving supports at width 22.
Inactive pairs never contribute an interval or require a range certificate. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds

set_option maxRecDepth 100000

/-- On 21111 and 3111 the nonsingleton block, when present in an active pair,
is the left block. The only right block size is one. -/
abbrev TwoTreePair (a b : ℕ) : Prop := b = 1 ∧ (a = 1 ∨ a = 2 ∨ a = 3)

theorem twoTreePair_of_active {w : Word} (hw : w = .twoOneOneOneOne ∨ w = .threeOneOneOne)
    {i j : Fin 6} (hp : active w i j) : TwoTreePair (sizeAt w i) (sizeAt w j) := by
  rcases hw with rfl | rfl <;> revert i j <;> decide

/-- For the remaining words, use cached intervals for the three actual pair
sizes, and fall back to proven continuous enclosures for every other size. -/
private def restrictedLookup (idx : RangeIndex) : Lookup := fun a b j l r =>
  if TwoTreePair a b then lookupIn idx a b j l r else atlasBlockRange a b j l r

def twoTreeLookup : Lookup := restrictedLookup claimIndex

private theorem restrictedLookup_sound {idx : RangeIndex}
    (hall : ∀ c ∈ idx.entries, TwoTreePair c.a c.b → RangeValid c)
    (a b : ℕ) (j : Order) (l r : ℕ) (hl : l ≤ r) (hr : r ≤ 32000)
    (t : ℝ) (ht : t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000)) :
    (restrictedLookup idx a b j l r).Mem (blockValue a b (orderIndex j) t) := by
  unfold restrictedLookup
  split_ifs with hpair
  · unfold lookupIn
    split
    next c hc =>
      obtain ⟨hm,rfl,rfl,ho,rfl,rfl⟩ := RangeIndex.find?_spec hc
      exact hall c hm hpair j ho t ht
    next => exact atlasBlockRange_sound a b j hl hr ht
  · exact atlasBlockRange_sound a b j hl hr ht

theorem twoTreeLookup_sound
    (hall : ∀ c ∈ claimIndex.entries, TwoTreePair c.a c.b → RangeValid c)
    (a b : ℕ) (j : Order) (l r : ℕ) (hl : l ≤ r) (hr : r ≤ 32000)
    (t : ℝ) (ht : t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000)) :
    (twoTreeLookup a b j l r).Mem (blockValue a b (orderIndex j) t) :=
  restrictedLookup_sound hall a b j l r hl hr t ht

/-- Congruence of the interval arithmetic using only active block pairs. -/
theorem quantities_congr_active (w : Word) (f g : Fin 6 → Fin 6 → Order → Interval)
    (h : ∀ i j, active w i j → ∀ o, f i j o = g i j o) (A B : Interval) (k : Quantity) :
    quantities w f A B k = quantities w g A B k := by
  let S (row : Fin 6 → Interval) : Interval := ⟨∑ i, (row i).lo, ∑ i, (row i).hi⟩
  let terms (p : Fin 6 → Fin 6 → Order → Interval) (v : Fin 6 → ℚ) (o : Order) :=
    S fun i => S fun j =>
      let c := pairSign w i j * (v j-v i)^orderIndex o
      if active w i j ∧ c ≠ 0 then (Interval.singleton c).mul (p i j o) else Interval.singleton 0
  have he (v : Fin 6 → ℚ) (o : Order) : terms f v o = terms g v o := by
    unfold terms
    apply congrArg S
    funext i
    apply congrArg S
    funext j
    dsimp only
    split <;> rename_i hc
    · rw [h i j hc.1 o]
    · rfl
  cases k with
  | feasible _ => rfl
  | score _ => exact congrArg (fun z => (A.add z).add B.neg) (he 0 .value)
  | gradient k => exact he (basisDir k) .first
  | curvature k => exact he (encodedDir k) .second

theorem twoTreeBounds_eq {w : Word} (hw : w = .twoOneOneOneOne ∨ w = .threeOneOneOne) :
    boundsFrom twoTreeLookup internalTicks witnessTicks w =
      boundsFrom checkedLookup internalTicks witnessTicks w := by
  funext B k
  apply quantities_congr_active
  intro i j hij o
  unfold twoTreeLookup restrictedLookup checkedLookup
  rw [if_pos (twoTreePair_of_active hw hij)]

end GaussianChains.Point22.Atlas
