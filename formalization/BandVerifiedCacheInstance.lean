import BandVerifiedCacheOracle
import BandVerifiedCacheLookup

namespace GaussianChains.Band.Fast

def anchorId : Slab → Fin 3
  | .narrow => 0 | .lower => 1 | .upper => 2

def packetCache (s : Slab) : RawOracle :=
  ⟨rawBox (anchorId s), lookupBox (anchorId s)⟩

end GaussianChains.Band.Fast
