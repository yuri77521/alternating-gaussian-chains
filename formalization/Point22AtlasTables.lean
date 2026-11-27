import Point22AtlasTablesNodes

/-! Shared fixed-point atlas table. Only integer operations are used to fill the
128001 Gaussian samples and all 32000 triplets of kernel rows. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains GaussianChains.Cert GaussianChains.Cert.Nodes GaussianChains.ImageBounds

def sampleArray : Array Ticks :=
  ((List.iterate step init 128001).map State.sample).toArray

def getSample (cache : Array Ticks) (p : ℕ) := (cache[p]?).getD ⟨0,0⟩

theorem sampleArray_eq {p : ℕ} (hp : p ≤ 128000) :
    (getSample sampleArray p).decode work = (gaussianEntry work param p).sample := by
  have h : p < sampleArray.size := by
    simp only [sampleArray, List.size_toArray, List.length_map, List.length_iterate]
    omega
  rw [getSample, getElem?_pos sampleArray p h]
  simp only [Option.getD_some, sampleArray, List.getElem_toArray, List.getElem_map,
    List.getElem_iterate]
  exact congrArg Entry.sample (iterate_eq p)

structure Orders where
  value : Ticks
  first : Ticks
  second : Ticks
  deriving Repr, DecidableEq

def Orders.atOrder (v : Orders) : Order → Ticks
  | .value => v.value
  | .first => v.first
  | .second => v.second

def orders (sample : ℕ → Ticks) (p : ℕ) : Orders :=
  ⟨row sample .value p, row sample .first p, row sample .second p⟩

def table : Array Orders :=
  let cache := sampleArray
  Array.ofFn (n:=32000) (fun p => orders (getSample cache) p)

def atlasRow (ord : Order) (p : ℕ) : Ticks :=
  ((table[p]?).map (fun v => v.atOrder ord)).getD ⟨0,0⟩

theorem atlasRow_eq (ord : Order) {p : ℕ} (hp : p < 32000) :
    atlasRow ord p = row (getSample sampleArray) ord p := by
  simp only [atlasRow, table, Array.getElem?_ofFn, dif_pos hp, Option.map_some, Option.getD_some]
  cases ord <;> rfl

theorem atlasRow_sound (ord : Order) {p : ℕ} (hp : p < 32000) :
    ((atlasRow ord p).decode unit).Mem
      ((deriv^[orderIndex ord] (kernel 22)) ((p:ℝ)/32000)) := by
  rw [atlasRow_eq ord hp]
  exact row_sound (fun _ hi => sampleArray_eq hi) ord hp

#print axioms atlasRow_sound

end GaussianChains.Point22.Atlas.Tables

