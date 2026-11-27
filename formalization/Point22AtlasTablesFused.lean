import Point22AtlasTablesChecks

/-! Unrolled seven-image evaluation for the frozen grid. Each distinct image sample
is shared by all three multiplier orders. The reference finite-sum specification
remains the mathematical source of the node bounds. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains.ImageBounds

structure ThreeTicks where
  value : Ticks
  first : Ticks
  second : Ticks

def ThreeTicks.atOrder (v : ThreeTicks) : Order → Ticks
  | .value => v.value | .first => v.first | .second => v.second

private def plus (v w : Ticks) : Ticks := ⟨v.lo+w.lo,v.hi+w.hi⟩
private def combine (v w : ThreeTicks) : ThreeTicks :=
  ⟨plus v.value w.value, plus v.first w.first, plus v.second w.second⟩

private def scaleTicks (w : ℤ) (v : Ticks) : Ticks :=
  let a := w*v.lo
  let b := w*v.hi
  ⟨min a b, max a b⟩

private theorem scaleTicks_eq (w : ℤ) (v : Ticks) :
    scaleTicks w v = Ticks.rawMul ⟨w,w⟩ v := by
  simp [scaleTicks,Ticks.rawMul]

private def image3 (sample : ℕ → Ticks) (p : ℕ) (k : ℤ) : ThreeTicks :=
  let m := (p:ℤ) + k*32000
  let v := sample m.natAbs
  let w := 44*m
  ⟨scaleTicks (32000^2) v, scaleTicks (-w*32000) v,
    scaleTicks (w^2-44*32000^2) v⟩

private theorem image3_atOrder (sample : ℕ → Ticks) (p : ℕ) (k : ℤ) (j : Order) :
    (image3 sample p k).atOrder j = term sample j p k := by
  cases j <;> simp [image3, ThreeTicks.atOrder, term, weight,pos,scaleTicks_eq]

private theorem combine_atOrder (x y : ThreeTicks) (j : Order) :
    (combine x y).atOrder j = plus (x.atOrder j) (y.atOrder j) := by cases j <;> rfl

private def allImages (sample : ℕ → Ticks) (p : ℕ) : ThreeTicks :=
  let atK := image3 sample p
  combine (combine (combine (atK (-3)) (atK (-2))) (combine (atK (-1)) (atK 0)))
    (combine (atK 1) (combine (atK 2) (atK 3)))

private theorem sumSeven (f : ℤ → ℤ) :
    ∑ k ∈ Finset.Icc (-3:ℤ) 3, f k =
    ((f (-3)+f (-2))+(f (-1)+f 0))+(f 1+(f 2+f 3)) := by
  have h : Finset.Icc (-3:ℤ) 3 = {-3,-2,-1,0,1,2,3} := by decide
  rw [h]
  norm_num
  ring

private theorem allImages_atOrder (sample : ℕ → Ticks) (p : ℕ) (j : Order) :
    (allImages sample p).atOrder j = total sample j p := by
  simp [allImages,combine_atOrder,image3_atOrder,plus,total,sumSeven]

def fusedRows (sample : ℕ → Ticks) (p : ℕ) : ThreeTicks :=
  let v := allImages sample p
  ⟨roundRow v.value,roundRow v.first,roundRow v.second⟩

theorem fusedRows_eq (sample : ℕ → Ticks) (p : ℕ) (j : Order) :
    (fusedRows sample p).atOrder j = row sample j p := by
  cases j with
  | value => exact congrArg roundRow (allImages_atOrder sample p .value)
  | first => exact congrArg roundRow (allImages_atOrder sample p .first)
  | second => exact congrArg roundRow (allImages_atOrder sample p .second)

def fusedRowOK (p : ℕ) : Bool :=
  let v := fusedRows savedSample p
  decide (verifiedRow .value p = v.value ∧ verifiedRow .first p = v.first ∧
    verifiedRow .second p = v.second)

theorem fusedRowOK_eq (p : ℕ) : fusedRowOK p = rowOK p := by
  change decide (_ = (fusedRows savedSample p).atOrder .value ∧
    _ = (fusedRows savedSample p).atOrder .first ∧
    _ = (fusedRows savedSample p).atOrder .second) = _
  simp only [fusedRows_eq,rowOK]

theorem Checked.of_fused_segment {lo count : ℕ} (h : segmentOK fusedRowOK lo count = true) :
    Checked rowOK lo (lo+count) := by
  rw [← (funext fusedRowOK_eq : fusedRowOK = rowOK)]
  exact Checked.of_segment h

end GaussianChains.Point22.Atlas.Tables
