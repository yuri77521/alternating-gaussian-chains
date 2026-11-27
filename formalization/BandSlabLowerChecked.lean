import BandRowsLower19
import BandRowsLower37
import BandRowsLower53
import BandRowsLower68
import BandRowsLower82
import BandRowsLower95
import BandRowsLower107
import BandRowsLower118
import BandRowsLower128
import BandRowsLower137
import BandRowsLower146
import BandRowsLower154
import BandRowsLower161
import BandRowsLower168
import BandRowsLower174
import BandRowsLower180
import BandRowsLower185
import BandRowsLower190
import BandRowsLower194
import BandRowsLower198
import BandRowsLower202
import BandRowsLower206
import BandRowsLower210
import BandRowsLower213
import BandRowsLower216
import BandRowsLower218
import BandRowsLower220
import BandRowsLower222
import BandRowsLower224
import BandRowsLower226
import BandRowsLower227
import BandRowsLower228
import BandRowsLower229
import BandRowsLower230
import BandRowsLower231
import BandRowsLower232
import BandRowsLower233
import BandRowsLower234
import BandRowsLower235
import BandRowsLower236
import BandRowsLower237
import BandRowsLower238
import BandRowsLower239
import BandRowsLower240
import BandRowsLower241
import BandRowsLower242
import BandRowsLower243
import BandRowsLower244
import BandRowsLower245
import BandVerifiedCacheValidity
import BandVerifiedCacheProof1

namespace GaussianChains.Band.Material

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowerOfValid (V : Fast.Valid .lower (Fast.packetCache .lower))
    (b : Fin Slab.lower.count) (i : Fin 18) : RowExcluded .lower b i := by
  fin_cases b
  · exact floor1_0 V i
  · exact floor1_1 V i
  · exact floor1_2 V i
  · exact floor1_3 V i
  · exact floor1_4 V i
  · exact floor1_5 V i
  · exact floor1_6 V i
  · exact floor1_7 V i
  · exact floor1_8 V i
  · exact floor1_9 V i
  · exact floor1_10 V i
  · exact floor1_11 V i
  · exact floor1_12 V i
  · exact floor1_13 V i
  · exact floor1_14 V i
  · exact floor1_15 V i
  · exact floor1_16 V i
  · exact floor1_17 V i
  · exact floor1_18 V i
  · exact floor1_19 V i
  · exact floor1_20 V i
  · exact floor1_21 V i
  · exact floor1_22 V i
  · exact floor1_23 V i
  · exact floor1_24 V i
  · exact floor1_25 V i
  · exact floor1_26 V i
  · exact floor1_27 V i
  · exact floor1_28 V i
  · exact floor1_29 V i
  · exact floor1_30 V i
  · exact floor1_31 V i
  · exact floor1_32 V i
  · exact floor1_33 V i
  · exact floor1_34 V i
  · exact floor1_35 V i
  · exact floor1_36 V i
  · exact floor1_37 V i
  · exact floor1_38 V i
  · exact floor1_39 V i
  · exact floor1_40 V i
  · exact floor1_41 V i
  · exact floor1_42 V i
  · exact floor1_43 V i
  · exact floor1_44 V i
  · exact floor1_45 V i
  · exact floor1_46 V i
  · exact floor1_47 V i
  · exact floor1_48 V i

theorem lowerChecked (b : Fin Slab.lower.count) (i : Fin 18) : RowExcluded .lower b i :=
  lowerOfValid (Fast.packetCache_valid .lower Fast.checkedAnchor1) b i

#print axioms lowerChecked
end GaussianChains.Band.Material
