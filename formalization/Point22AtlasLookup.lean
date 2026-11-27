import Point22AtlasClaims
import Point22AtlasKernel

/-! Separate finite tree arithmetic from the substantive interval-table obligation.
An unlisted key falls back to the mathematically specified block range. -/

namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds

def lookupIn (idx : RangeIndex) (a b : ℕ) (j : Order) (l r : ℕ) : Interval :=
  match idx.find? a b (orderIndex j) l r with
  | some c => ofTicks c.lo c.hi
  | none => atlasBlockRange a b j l r

/-- Mathematical statement needed for a stored range: every real displacement in
its *closed* query interval is enclosed, with the signed sites inside the blocks. -/
def RangeValid (c : RangeClaim) : Prop :=
  ∀ j : Order, c.ord = orderIndex j → ∀ t ∈ Set.Icc ((c.L:ℝ)/32000) ((c.R:ℝ)/32000),
    (ofTicks c.lo c.hi).Mem (blockValue c.a c.b (orderIndex j) t)

theorem lookupIn_sound {idx : RangeIndex} (hall : ∀ c ∈ idx.entries, RangeValid c)
    (a b : ℕ) (j : Order) (l r : ℕ) (hl : l ≤ r) (hr : r ≤ 32000)
    (t : ℝ) (ht : t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000)) :
    (lookupIn idx a b j l r).Mem (blockValue a b (orderIndex j) t) := by
  unfold lookupIn
  split
  next c hc =>
    obtain ⟨hm, rfl, rfl, ho, rfl, rfl⟩ := RangeIndex.find?_spec hc
    exact hall c hm j ho t ht
  next =>
    exact atlasBlockRange_sound a b j hl hr ht

def checkedLookup := lookupIn claimIndex

theorem checkedLookup_sound (hall : ∀ c ∈ claimIndex.entries, RangeValid c)
    (a b : ℕ) (j : Order) (l r : ℕ) (hl : l ≤ r) (hr : r ≤ 32000)
    (t : ℝ) (ht : t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000)) :
    (checkedLookup a b j l r).Mem (blockValue a b (orderIndex j) t) :=
  lookupIn_sound (idx := claimIndex) hall a b j l r hl hr t ht

end GaussianChains.Point22.Atlas
