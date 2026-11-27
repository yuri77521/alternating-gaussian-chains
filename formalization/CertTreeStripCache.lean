import CertTreeStripOracle
import CertTreeGridCache
import CertTreeRangeCache
import CertTreeTaylorSample

set_option maxRecDepth 65536

/-! The materialized spatial oracle. Its three sparse ranges and its raw
samples are constructed once per reference width. -/
namespace GaussianChains.Cert.Tables
open GaussianChains.ImageBounds GaussianChains.FourierBounds

private abbrev M : ℕ+ := 8192
private abbrev U : ℕ+ := 1000000000
private abbrev D : ℕ+ := 10^32

abbrev RangeCache := Array (Array Interval)

def paddedRows (j : Order) (table : Array NodeOrders) : Array Interval :=
  table.map fun r => paddedNode M U (stripCap j) (fun _ => r.atOrder j) 0

structure StripCache where
  table : Array NodeOrders
  values : RangeCache
  slopes : RangeCache
  curvatures : RangeCache

private def makeCache (t : Array NodeOrders) : StripCache :=
  ⟨t, buildRangeCache (paddedRows .value t), buildRangeCache (paddedRows .first t),
   buildRangeCache (paddedRows .second t)⟩

def buildStripCache (s : ℚ) : StripCache := makeCache (gridTable D U M s)

def StripCache.ranges (C : StripCache) : Order → RangeCache
  | .value => C.values
  | .first => C.slopes
  | .second => C.curvatures

def StripCache.query (C : StripCache) (j : Order) (left right : ℚ) : Interval :=
  rangeCached (C.ranges j) (nearest M left) (nearest M right)

private theorem make_ranges (t : Array NodeOrders) (j : Order) :
    (makeCache t).ranges j = buildRangeCache (paddedRows j t) := by cases j <;> rfl

private theorem build_ranges (s : ℚ) (j : Order) :
    (buildStripCache s).ranges j = buildRangeCache (paddedRows j (gridTable D U M s)) :=
  make_ranges (gridTable D U M s) j

private theorem get_paddedRows (s : ℚ) (j : Order) {p : ℕ} (hp : p ≤ 8192) :
    getNode (paddedRows j (gridTable D U M s)) p = paddedNode M U (stripCap j) (stripNode s j) p := by
  have hsz : p < (gridTable D U M s).size := by rw [gridTable_size]; exact Nat.lt_succ_of_le hp
  have hsz' : p < (paddedRows j (gridTable D U M s)).size := by simpa [paddedRows] using hsz
  rw [getNode, Array.getElem?_eq_getElem hsz', Option.getD_some]
  simp only [paddedRows, Array.getElem_map, paddedNode, stripNode]
  rw [gridTable_eq D U M s j hp] <;> simp only [D, U, M, show (10:ℕ+)^9 = 1000000000 by decide +kernel]

theorem cachedStripRange_sound {s : ℚ} (hs : s ∈ Set.Icc (8:ℚ) 9) (j : Order)
    {left right : ℚ} (hl : 0 ≤ left) (hr : right ≤ 1) {x : ℝ}
    (hx : (left:ℝ) ≤ x ∧ x ≤ (right:ℝ)) :
    ((buildStripCache s).query j left right).Mem ((deriv^[orderIndex j] (kernel (s:ℝ))) x) := by
  have hs' : (s:ℝ) ∈ Set.Icc (8:ℝ) 9 := ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩
  have hs0 : 0 < (s:ℝ) := by linarith [hs'.1]
  have hL : nearest M left ≤ nearestReal M x := by rw [← nearest_cast]; exact nearestReal_mono M hx.1
  have hR : nearestReal M x ≤ nearest M right := by rw [← nearest_cast]; exact nearestReal_mono M hx.2
  have hl' : (0:ℝ) ≤ left := by exact_mod_cast hl
  have hr' : (right:ℝ) ≤ 1 := by exact_mod_cast hr
  have hlast : nearest M right ≤ 8192 := by
    rw [← nearest_cast]
    exact (nearest_bound (M:=M) ((hl'.trans hx.1).trans hx.2) hr').1
  rw [StripCache.query, build_ranges, rangeCached_eq _ (hL.trans hR) (by
    simp [paddedRows,gridTable_size]; exact Nat.lt_succ_of_le hlast)]
  apply rangeHull_mem hL hR
  rw [get_paddedRows s j (hR.trans hlast)]
  apply paddedNode_mem (by cases j <;> norm_num [stripCap])
    (kernel_differentiable_order hs0 _) _ _ _
    (fun p hp => gridNode_strip_sound _ _ hs j hp) (hl'.trans hx.1) (hx.2.trans hr')
  intro t
  obtain ⟨h₁,h₂,h₃⟩ := strip_derivative_caps hs' t
  cases j with
  | value => simpa [orderIndex,stripCap] using h₁.le
  | first => simpa [orderIndex,stripCap,Function.iterate_succ_apply'] using h₂.le
  | second => simpa [orderIndex,stripCap,Function.iterate_succ_apply'] using h₃.le

private def fallback : NodeOrders := ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩

def StripCache.node (C : StripCache) (j : Order) (p : ℕ) : Interval :=
  ((C.table[p]?).getD fallback).atOrder j

private theorem make_node (t : Array NodeOrders) (j : Order) (p : ℕ) (hp : p < t.size) :
    (makeCache t).node j p = t[p].atOrder j := by
  change (t[p]?.getD fallback).atOrder j = _
  rw [Array.getElem?_eq_getElem hp, Option.getD_some]

theorem cachedStripNode_eq (s : ℚ) (j : Order) {p : ℕ} (hp : p ≤ 8192) :
    (buildStripCache s).node j p = stripNode s j p := by
  have hsz : p < (gridTable D U M s).size := by rw [gridTable_size]; exact Nat.lt_succ_of_le hp
  exact (make_node (gridTable D U M s) j p hsz).trans (gridTable_eq D U M s j hp)

def StripCache.taylor (C : StripCache) (q : ℚ) : ℚ := taylorAt M U (C.node .value) (C.node .first) q

def StripCache.accurate (C : StripCache) (q : ℚ) : Bool :=
  midpointOK U (C.node .value (nearest M q)) && midpointOK U (C.node .first (nearest M q))

/-- A width may check sample accuracy once for its entire table. -/
def StripCache.accurateAll (C : StripCache) : Bool :=
  C.table.all fun r => midpointOK U r.value && midpointOK U r.first

theorem accurate_of_all {C : StripCache} {q : ℚ} (h : C.accurateAll = true)
    (hi : nearest M q < C.table.size) : C.accurate q = true := by
  have hh := (Array.all_eq_true.mp h) (nearest M q) hi
  simpa [StripCache.accurate, StripCache.node, NodeOrders.atOrder, Array.getElem?_eq_getElem hi] using hh

theorem cachedStripTaylor_sound {s q : ℚ} (hs : s ∈ Set.Icc (8:ℚ) 9)
    (hq : q ∈ Set.Icc (0:ℚ) 1) (checked : (buildStripCache s).accurate q = true) :
    |kernel (s:ℝ) (q:ℝ) - ((buildStripCache s).taylor q:ℝ)| ≤ (taylorBudget M U 20:ℝ) := by
  have hs' : (s:ℝ) ∈ Set.Icc (8:ℝ) 9 := ⟨by exact_mod_cast hs.1, by exact_mod_cast hs.2⟩
  have hs0 : 0 < (s:ℝ) := by linarith [hs'.1]
  have hp : nearest M q ≤ 8192 := by
    rw [← nearest_cast]
    exact (nearest_bound (M:=M) (by exact_mod_cast hq.1) (by exact_mod_cast hq.2)).1
  have hD (n : ℕ) (x : ℝ) := (kernel_differentiable_order hs0 n x).hasDerivAt
  simp only [StripCache.accurate, Bool.and_eq_true] at checked
  apply taylorAt_sound (K:=20) (f:=kernel (s:ℝ))
    (f':=deriv (kernel (s:ℝ))) (f'':=deriv^[2] (kernel (s:ℝ)))
    (by norm_num) (hD 0) (hD 1) (fun t => (strip_derivative_caps hs' t).2.1.le)
    M U hq _ _ checked.1 checked.2
  · rw [cachedStripNode_eq s .value hp]
    exact gridNode_strip_sound D M hs .value hp
  · rw [cachedStripNode_eq s .first hp]
    exact gridNode_strip_sound D M hs .first hp

#print axioms cachedStripRange_sound
#print axioms cachedStripTaylor_sound

end GaussianChains.Cert.Tables
