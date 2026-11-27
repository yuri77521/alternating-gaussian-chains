import Point22AtlasTablesTypes
import Point22AtlasIndex

/-! Integer enclosure of a contiguous run of signed block-kernel samples.
The data supplying the claimed endpoints are checked at the leaves.
Larger dyadic runs reuse the proofs for their two children. -/

namespace GaussianChains.Point22.Atlas.RangeTicks
open GaussianChains.ImageBounds GaussianChains.Point22.Atlas.Tables

def slot (p i j : ℕ) : ℕ := (((p:ℤ) + ((j:ℤ)-i)*32) % 32000).toNat

def signed (i j : ℕ) (v : Ticks) : Ticks :=
  if (i+j)%2=0 then v else ⟨-v.hi,-v.lo⟩

def rawBlock (node : Order → ℕ → Ticks) (a b : ℕ) (ord : Order) (p : ℕ) : Ticks :=
  let get (i j : ℕ) := signed i j (node ord (slot p i j))
  ⟨∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, (get i j).lo,
   ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, (get i j).hi⟩

def Contains (outer inner : Ticks) := outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi

instance (outer inner : Ticks) : Decidable (Contains outer inner) := inferInstanceAs
  (Decidable (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi))

theorem Contains.trans {x y z : Ticks} (h : Contains x y) (h' : Contains y z) : Contains x z :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

def Run (f : ℕ → Ticks) (start count : ℕ) (v : Ticks) :=
  ∀ p, start ≤ p → p < start+count → Contains v (f p)

def checkRun (f : ℕ → Ticks) (start length : ℕ) (v : Ticks) : Bool :=
  (List.range length).all (fun i => decide (Contains v (f (start+i))))

theorem of_check {f : ℕ → Ticks} {start length : ℕ} {v : Ticks}
    (h : checkRun f start length v = true) : Run f start length v := by
  intro p hp hpl
  have hi : p-start ∈ List.range length := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h (p-start) hi
  simpa [Nat.add_sub_of_le hp] using (of_decide_eq_true hh)

theorem widen {f : ℕ → Ticks} {start len : ℕ} {v w : Ticks}
    (h : Run f start len v) (hw : Contains w v) : Run f start len w :=
  fun p hp hpl => hw.trans (h p hp hpl)

theorem append {f : ℕ → Ticks} {start m n : ℕ} {v : Ticks}
    (l : Run f start m v) (r : Run f (start+m) n v) : Run f start (m+n) v := by
  intro p hp hpl
  by_cases h : p < start+m
  · exact l p hp h
  · exact r p (by omega) (by omega)

/-- Join adjacent verified runs after checking that the parent covers both
child intervals. Arguments reduce only small integer endpoint comparisons. -/
theorem join {f : ℕ → Ticks} {start m n : ℕ} {v vl vr : Ticks}
    (l : Run f start m vl) (r : Run f (start+m) n vr)
    (hl : Contains v vl) (hr : Contains v vr) : Run f start (m+n) v :=
  append (widen l hl) (widen r hr)

def padTicks (a b : ℕ) (ord : Order) : ℤ :=
  let cap : ℤ := match ord with | .value => 44 | .first => 1500 | .second => 22000
  Neg.neg (-((a:ℤ)*b*cap*10^11) / (8*32000^2))

def inflate (t : Ticks) (e : ℤ) : Ticks := ⟨t.lo-e,t.hi+e⟩
def deflate (t : Ticks) (e : ℤ) : Ticks := ⟨t.lo+e,t.hi-e⟩

def ofIndex : ℕ → Order
  | 0 => .value
  | 1 => .first
  | _ => .second

def CheckedClaim (node : Order → ℕ → Ticks) (c : RangeClaim) : Prop :=
  Run (rawBlock node c.a c.b (ofIndex c.ord)) c.L (c.R+1-c.L)
    (deflate ⟨c.lo,c.hi⟩ (padTicks c.a c.b (ofIndex c.ord)))

def Every (P : RangeClaim → Prop) : RangeIndex → Prop
  | .leaf r => P r
  | .fork _ l r => Every P l ∧ Every P r

theorem every_mem {P : RangeClaim → Prop} {idx : RangeIndex} (h : Every P idx) :
    ∀ c ∈ idx.entries, P c := by
  induction idx with
  | leaf r =>
    intro c hc
    obtain rfl : c = r := List.mem_singleton.mp hc
    exact h
  | fork k l r il ir =>
    intro c hc
    rcases List.mem_append.mp hc with hh | hh
    · exact il h.1 c hh
    · exact ir h.2 c hh

#print axioms of_check

end GaussianChains.Point22.Atlas.RangeTicks

