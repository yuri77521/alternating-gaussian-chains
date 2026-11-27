import BandVerifiedCacheProof0
import BandVerifiedCacheProof1
import BandVerifiedCacheProof2
import BandVerifiedCacheValidity

namespace GaussianChains.Band.Fast

/-- Each physical width in the strip uses the exact same packed data as
its executable packet replay. -/
theorem certifiedPacketCache (s : Slab) : Valid s (packetCache s) := by
  apply packetCache_valid
  cases s
  · exact checkedAnchor0
  · exact checkedAnchor1
  · exact checkedAnchor2

#print axioms certifiedPacketCache

end GaussianChains.Band.Fast
