import Point22AtlasLookup
import Point22AtlasReplay

namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds

def atlasAccept (w : Word) : Bool :=
  replay w (boundsFrom checkedLookup internalTicks witnessTicks w) (rootBox w) (tree w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem six_block_accept : atlasAccept .six = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_triples_accept : atlasAccept .threeThree = true := by decide +kernel

end GaussianChains.Point22.Atlas
