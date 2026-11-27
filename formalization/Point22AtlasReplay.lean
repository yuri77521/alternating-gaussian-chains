import Point22AtlasTree
import Point22AtlasQuantities
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp

/-! Integer query indices, continuous range soundness and composition with the tree. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds

abbrev Lookup := ℕ → ℕ → Order → ℕ → ℕ → Interval

def lowerIndex (v : ℚ) : ℕ := ⌊v⌋.toNat
def upperIndex (v : ℚ) : ℕ := min 32000 ⌈v⌉.toNat

private theorem lowerIndex_le {v : ℚ} {t : ℝ} (ht : 0 ≤ t) (hv : (v:ℝ) ≤ t) :
    (lowerIndex v : ℝ) ≤ t := by
  unfold lowerIndex
  by_cases h : 0 ≤ ⌊v⌋
  · have hc : (((⌊v⌋.toNat:ℕ):ℝ)) = ((⌊v⌋:ℤ):ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h
    rw [hc]
    exact (show ((⌊v⌋:ℤ):ℝ) ≤ (v:ℝ) by exact_mod_cast Int.floor_le v).trans hv
  · have hh : ⌊v⌋.toNat = 0 := by omega
    simpa [hh] using ht

private theorem le_upperIndex {v : ℚ} {t : ℝ} (ht : t ≤ 32000) (hv : t ≤ (v:ℝ)) :
    t ≤ (upperIndex v : ℝ) := by
  have hh : ((⌈v⌉:ℤ):ℝ) ≤ (⌈v⌉.toNat : ℕ) := by exact_mod_cast Int.self_le_toNat ⌈v⌉
  have hq : (v:ℝ) ≤ ((⌈v⌉:ℤ):ℝ) := by exact_mod_cast Int.le_ceil v
  simpa [upperIndex] using le_min ht (hv.trans (hq.trans hh))

def span (w : Word) (i j : Fin 6) : ℕ := startLabel w j - startLabel w i

def lowerQuery (w : Word) (B : Box 6) (i j : Fin 6) : ℕ :=
  lowerIndex (max ((B j).lo-(B i).hi) (32*span w i j))

def upperQuery (w : Word) (B : Box 6) (i j : Fin 6) : ℕ :=
  upperIndex (min ((B j).hi-(B i).lo) (32000 - 32*((6-span w i j:ℕ):ℚ)))

def SpanTicks (w : Word) (x : Fin 6 → ℝ) : Prop :=
  ∀ i j, active w i j →
    32*(span w i j:ℝ) ≤ x j - x i ∧ x j - x i ≤ 32000 - 32*(6-span w i j : ℕ)

noncomputable def meshToPhysical (x : Fin 6 → ℝ) (i : Fin 6) := x i / 32000

def boundsFrom (lookup : Lookup) (internal : Word → Interval) (witness : Interval)
    (w : Word) (B : Box 6) : Quantity → Interval :=
  quantities w (fun i j ord => lookup (sizeAt w i) (sizeAt w j) ord
    (lowerQuery w B i j) (upperQuery w B i j)) (internal w) witness

theorem boundsFrom_sound {lookup : Lookup} {internal : Word → Interval} {witness : Interval}
    {si sw : ℝ} {w : Word} {B : Box 6} {x : Fin 6 → ℝ}
    (hb : B.Mem x) (hs : SpanTicks w x)
    (hi : (internal w).Mem si) (hw : witness.Mem sw)
    (hr : ∀ (a b : ℕ) (j : Order) (l r : ℕ), l ≤ r → r ≤ 32000 → ∀ t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000),
      (lookup a b j l r).Mem (blockValue a b (orderIndex j) t))
    (k : Quantity) :
    (boundsFrom lookup internal witness w B k).Mem (realQuantity w (meshToPhysical x) si sw k) := by
  apply quantities_sound _ _ hi hw
  intro i j hij ord
  obtain ⟨hl,hu⟩ := hs i j hij
  have ht₀ : 0 ≤ x j - x i := (by positivity : 0 ≤ 32*(span w i j:ℝ)).trans hl
  have ht₁ : x j - x i ≤ 32000 := hu.trans (by linarith [Nat.cast_nonneg (α:=ℝ) (6-span w i j)])
  have hlo : (lowerQuery w B i j:ℝ) ≤ x j - x i := by
    apply lowerIndex_le ht₀
    push_cast
    exact max_le (by linarith [(hb j).1,(hb i).2]) hl
  have hhi : x j - x i ≤ (upperQuery w B i j:ℝ) := by
    apply le_upperIndex ht₁
    push_cast
    exact le_min (by linarith [(hb j).2,(hb i).1]) hu
  have hlr : lowerQuery w B i j ≤ upperQuery w B i j := by exact_mod_cast hlo.trans hhi
  apply hr _ _ _ _ _ hlr (min_le_left _ _)
  constructor <;> unfold meshToPhysical <;> linarith only [hlo,hhi]

/-- A verified range table and acceptance of the entire frozen tree imply that each eligible
physical candidate lies in a surviving local box. The table proof is a required premise. -/
theorem classify_of_replay {lookup : Lookup} {internal : Word → Interval} {witness : Interval}
    {w : Word} {x : Fin 6 → ℝ} {si sw : ℝ}
    (hr : ∀ (a b : ℕ) (j : Order) (l r : ℕ), l ≤ r → r ≤ 32000 → ∀ t ∈ Set.Icc ((l:ℝ)/32000) ((r:ℝ)/32000),
      (lookup a b j l r).Mem (blockValue a b (orderIndex j) t))
    (hi : (internal w).Mem si) (hw : witness.Mem sw)
    (ho : OrderedTicks w x) (hc : CanonicalTicks w x) (hs : SpanTicks w x)
    (hx : (rootBox w).Mem x)
    (necessary : ∀ k, Necessary k (realQuantity w (meshToPhysical x) si sw k))
    (checked : replay w (boundsFrom lookup internal witness w) (rootBox w) (tree w) = true) :
    w = .threeOneOneOne ∧ localTarget.Mem x := by
  apply replay_sound ho hc _ _ _ hx checked
  intro B hb k _ hk
  exact violates_sound k hk (boundsFrom_sound hb hs hi hw hr k) (necessary k)

end GaussianChains.Point22.Atlas
