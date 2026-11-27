import Point22AtlasData

/-! Counts of the actual Lean trees, independent of the extractor's counters. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

def treeSize : Tree 6 → ℕ
  | .split _ _ l r => 1 + treeSize l + treeSize r
  | _ => 1

def localLeaves : Tree 6 → ℕ
  | .localDomain => 1
  | .split _ _ l r => localLeaves l + localLeaves r
  | _ => 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem atlas_size : (words.map (fun w => treeSize (tree w))).sum = 5638 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem atlas_local_leaf_count (w : Word) :
    localLeaves (tree w) = if w = .threeOneOneOne then 6 else 0 := by
  cases w <;> decide +kernel

end GaussianChains.Point22.Atlas
