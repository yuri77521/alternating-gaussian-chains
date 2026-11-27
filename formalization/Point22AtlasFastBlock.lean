import Point22AtlasRangeTicks
import Mathlib.Tactic.Ring

/-! The frozen atlas uses ten pairs of block sizes. Evaluate each distinct
mesh shift once. Equal shifts have the same sign, so integer endpoint sums
agree exactly with the general double sum. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open GaussianChains.ImageBounds GaussianChains.Point22.Atlas.Tables

private def getSlot (node : Order → ℕ → Ticks) (ord : Order) (p : ℕ) (offset : ℤ) :=
  node ord (((p:ℤ)+offset)%32000).toNat

def fastBlock (node : Order → ℕ → Ticks) (a b : ℕ) (ord : Order) (p : ℕ) : Ticks :=
  match a,b with
  | 1, 1 =>
    let v0 := getSlot node ord p 0
    v0
  | 1, 2 =>
    let v0 := getSlot node ord p 0
    let v1 := getSlot node ord p 32
    ⟨v0.lo - v1.hi, v0.hi - v1.lo⟩
  | 2, 1 =>
    let v0 := getSlot node ord p (-32)
    let v1 := getSlot node ord p 0
    ⟨-v0.hi + v1.lo, -v0.lo + v1.hi⟩
  | 2, 2 =>
    let v0 := getSlot node ord p (-32)
    let v1 := getSlot node ord p 0
    let v2 := getSlot node ord p 32
    ⟨-v0.hi + 2*v1.lo - v2.hi, -v0.lo + 2*v1.hi - v2.lo⟩
  | 3, 1 =>
    let v0 := getSlot node ord p (-64)
    let v1 := getSlot node ord p (-32)
    let v2 := getSlot node ord p 0
    ⟨v0.lo - v1.hi + v2.lo, v0.hi - v1.lo + v2.hi⟩
  | 3, 2 =>
    let v0 := getSlot node ord p (-64)
    let v1 := getSlot node ord p (-32)
    let v2 := getSlot node ord p 0
    let v3 := getSlot node ord p 32
    ⟨v0.lo - 2*v1.hi + 2*v2.lo - v3.hi, v0.hi - 2*v1.lo + 2*v2.hi - v3.lo⟩
  | 3, 3 =>
    let v0 := getSlot node ord p (-64)
    let v1 := getSlot node ord p (-32)
    let v2 := getSlot node ord p 0
    let v3 := getSlot node ord p 32
    let v4 := getSlot node ord p 64
    ⟨v0.lo - 2*v1.hi + 3*v2.lo - 2*v3.hi + v4.lo, v0.hi - 2*v1.lo + 3*v2.hi - 2*v3.lo + v4.hi⟩
  | 4, 1 =>
    let v0 := getSlot node ord p (-96)
    let v1 := getSlot node ord p (-64)
    let v2 := getSlot node ord p (-32)
    let v3 := getSlot node ord p 0
    ⟨-v0.hi + v1.lo - v2.hi + v3.lo, -v0.lo + v1.hi - v2.lo + v3.hi⟩
  | 4, 2 =>
    let v0 := getSlot node ord p (-96)
    let v1 := getSlot node ord p (-64)
    let v2 := getSlot node ord p (-32)
    let v3 := getSlot node ord p 0
    let v4 := getSlot node ord p 32
    ⟨-v0.hi + 2*v1.lo - 2*v2.hi + 2*v3.lo - v4.hi, -v0.lo + 2*v1.hi - 2*v2.lo + 2*v3.hi - v4.lo⟩
  | 5, 1 =>
    let v0 := getSlot node ord p (-128)
    let v1 := getSlot node ord p (-96)
    let v2 := getSlot node ord p (-64)
    let v3 := getSlot node ord p (-32)
    let v4 := getSlot node ord p 0
    ⟨v0.lo - v1.hi + v2.lo - v3.hi + v4.lo, v0.hi - v1.lo + v2.hi - v3.lo + v4.hi⟩
  | _, _ => rawBlock node a b ord p

set_option maxRecDepth 10000 in
theorem fastBlock_eq_raw (node : Order → ℕ → Ticks) (a b : ℕ) (ord : Order) (p : ℕ) :
    fastBlock node a b ord p = rawBlock node a b ord p := by
  unfold fastBlock
  split <;> first | rfl | (norm_num [rawBlock, Finset.sum_range_succ, signed, slot, getSlot] <;>
    constructor <;> ring)

end GaussianChains.Point22.Atlas.RangeTicks

