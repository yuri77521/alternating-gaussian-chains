import BandRowsNarrow05
import BandRowsNarrow09
import BandRowsNarrow13
import BandRowsNarrow17
import BandRowsNarrow21
import BandRowsNarrow24
import BandRowsNarrow27
import BandRowsNarrow30
import BandRowsNarrow32
import BandRowsNarrow34
import BandRowsNarrow37
import BandRowsNarrow38
import BandRowsNarrow39
import BandRowsNarrow40
import BandVerifiedCacheValidity
import BandVerifiedCacheProof0

namespace GaussianChains.Band.Material

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem narrowOfValid (V : Fast.Valid .narrow (Fast.packetCache .narrow))
    (b : Fin Slab.narrow.count) (i : Fin 18) : RowExcluded .narrow b i := by
  fin_cases b
  · exact floor0_0 V i
  · exact floor0_1 V i
  · exact floor0_2 V i
  · exact floor0_3 V i
  · exact floor0_4 V i
  · exact floor0_5 V i
  · exact floor0_6 V i
  · exact floor0_7 V i
  · exact floor0_8 V i
  · exact floor0_9 V i
  · exact floor0_10 V i
  · exact floor0_11 V i
  · exact floor0_12 V i
  · exact floor0_13 V i

theorem narrowChecked (b : Fin Slab.narrow.count) (i : Fin 18) : RowExcluded .narrow b i :=
  narrowOfValid (Fast.packetCache_valid .narrow Fast.checkedAnchor0) b i

#print axioms narrowChecked
end GaussianChains.Band.Material
