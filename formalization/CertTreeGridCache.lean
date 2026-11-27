import CertTreeGrid
import Mathlib.Data.List.Iterate

/-! A whole spatial table shares one outward-rounded sequence of Gaussian
samples. The executable array lookup is equal to the reference recurrence at
every retained image of every grid node, including the two endpoints. -/

namespace GaussianChains.Cert.Tables

open Interval Nodes GaussianChains.ImageBounds

private def initial (scale : ℕ+) (a : ℚ) : Entry := ⟨singleton 1, seed scale a⟩

private def stepAt (scale : ℕ+) (a : ℚ) := advance scale (seed scale (2*a))

private theorem iter_eq (scale : ℕ+) (a : ℚ) (n : ℕ) :
    (stepAt scale a)^[n] (initial scale a) = gaussianEntry scale a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- Index i stores the sample for exp(-s i²/M²). Four periods suffice for all
seven images at any node p from zero through M. -/
def sampleCache (scale M : ℕ+) (s : ℚ) : Array Interval :=
  let a := s/(M:ℚ)^2
  ((List.iterate (stepAt scale a) (initial scale a) (4*(M:ℕ)+1)).map Entry.sample).toArray

def sampleAt (cache : Array Interval) (i : ℕ) : Interval :=
  (cache[i]?).getD (singleton 0)

theorem sampleAt_eq (scale M : ℕ+) (s : ℚ) {i : ℕ} (hi : i ≤ 4*(M:ℕ)) :
    sampleAt (sampleCache scale M s) i = (gaussianEntry scale (s/(M:ℚ)^2) i).sample := by
  have ha : i < (sampleCache scale M s).size := by simp [sampleCache]; omega
  unfold sampleAt
  rw [getElem?_pos (sampleCache scale M s) i ha]
  simp only [Option.getD_some, sampleCache, List.getElem_toArray, List.getElem_map,
    List.getElem_iterate, iter_eq]

private theorem index_le {p : ℕ} {M : ℕ+} (hp : p ≤ (M:ℕ)) {k : ℤ}
    (hk : k ∈ Finset.Icc (-3:ℤ) 3) : ((p:ℤ)+k*((M:ℕ):ℤ)).natAbs ≤ 4*(M:ℕ) := by
  obtain ⟨hl,hh⟩ := Finset.mem_Icc.mp hk
  have hm : (0:ℤ) ≤ (M:ℕ) := Int.natCast_nonneg _
  have hp₁ : (p:ℤ) ≤ (M:ℕ) := by exact_mod_cast hp
  have h₁ := mul_le_mul_of_nonneg_right hl hm
  have h₂ := mul_le_mul_of_nonneg_right hh hm
  have hi : |(p:ℤ)+k*(M:ℕ)| ≤ 4*(M:ℕ) := by
    apply abs_le.mpr
    constructor <;> linarith [Int.natCast_nonneg p]
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

/-- Pass the same cached array to all rows and derivative orders. -/
def cachedGridNode (cache : Array Interval) (unit M : ℕ+) (s : ℚ) (j : Order) (p : ℕ) : Interval :=
  assemble unit (weightedImage (sampleAt cache) M s j p)

theorem cachedGridNode_eq (scale unit M : ℕ+) (s : ℚ) (j : Order) {p : ℕ} (hp : p ≤ (M:ℕ)) :
    cachedGridNode (sampleCache scale M s) unit M s j p = gridNode scale unit M s j p := by
  apply assemble_congr
  intro k hk
  unfold weightedImage imageNode
  dsimp only
  rw [sampleAt_eq scale M s (index_le hp hk)]
  rfl

structure NodeOrders where
  value : Interval
  first : Interval
  second : Interval
  deriving Repr

def NodeOrders.atOrder (v : NodeOrders) : Order → Interval
  | .value => v.value
  | .first => v.first
  | .second => v.second

/-- Materialize all three output rows and share the input recurrence. -/
def gridTable (scale unit M : ℕ+) (s : ℚ) : Array NodeOrders :=
  let cache := sampleCache scale M s
  Array.ofFn (n:=(M:ℕ)+1) (fun p =>
    ⟨cachedGridNode cache unit M s .value p, cachedGridNode cache unit M s .first p,
     cachedGridNode cache unit M s .second p⟩)

theorem gridTable_size (scale unit M : ℕ+) (s : ℚ) :
    (gridTable scale unit M s).size = (M:ℕ)+1 := by simp [gridTable]

theorem gridTable_eq (scale unit M : ℕ+) (s : ℚ) (j : Order) {p : ℕ} (hp : p ≤ (M:ℕ)) :
    ((gridTable scale unit M s)[p]'(by rw [gridTable_size]; omega)).atOrder j =
      gridNode scale unit M s j p := by
  cases j <;> simp [gridTable, NodeOrders.atOrder, cachedGridNode_eq _ _ _ _ _ hp]

theorem gridTable_strip_sound (scale M : ℕ+) {s : ℚ} (hs : s ∈ Set.Icc (8:ℚ) 9)
    (j : Order) {p : ℕ} (hp : p ≤ (M:ℕ)) :
    (((gridTable scale 1000000000 M s)[p]'(by rw [gridTable_size]; omega)).atOrder j).Mem
      ((deriv^[orderIndex j] (GaussianChains.kernel (s:ℝ))) ((p:ℝ)/M)) := by
  rw [gridTable_eq _ _ _ _ _ hp]
  exact gridNode_strip_sound _ _ hs j hp

theorem gridTable_point_sound (scale unit M : ℕ+) (hu : (unit:ℕ) ≤ 100000000000)
    (j : Order) {p : ℕ} (hp : p ≤ (M:ℕ)) :
    (((gridTable scale unit M 22)[p]'(by rw [gridTable_size]; omega)).atOrder j).Mem
      ((deriv^[orderIndex j] (GaussianChains.kernel 22)) ((p:ℝ)/M)) := by
  rw [gridTable_eq _ _ _ _ _ hp]
  exact gridNode_point_sound _ _ _ hu j hp

#print axioms gridTable_strip_sound
#print axioms gridTable_point_sound

#print axioms gridTable_eq

end GaussianChains.Cert.Tables

