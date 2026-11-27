import BandVerifiedCacheInstance

/-! A real postfix packet from the first narrow strip, including its
centered value witnesses, evaluated by kernel reduction. -/
namespace GaussianChains.Band.Fast
open GaussianChains.Cert

private def centerLeaf (a b : ℕ) : Cover Witness :=
  .leaf (.centered ![grid a, 0, 0, 0, 0, grid b])

/-- The row at support zero and the first narrow width interval, in the
inductive tree format used by the covering theorem. -/
def firstTree : Cover Witness :=
  .split 0 (grid 2048)
    (.split 0 (grid 1024) (centerLeaf 512 7680) (centerLeaf 1536 6656))
    (.split 0 (grid 3072) (centerLeaf 2560 5632) (centerLeaf 3584 4608))

def firstPass : Bool := check
  (realTest .narrow (packetCache .narrow) (Slab.narrow.floor ⟨0, by decide⟩) (support 0) 4)
  (initial (support 0)) firstTree

set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
theorem first_row_checked : firstPass = true := by
  decide +kernel

#print axioms first_row_checked

end GaussianChains.Band.Fast
