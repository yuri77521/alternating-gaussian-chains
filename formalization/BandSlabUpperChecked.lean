import BandRowsUpper19
import BandRowsUpper36
import BandRowsUpper51
import BandRowsUpper65
import BandRowsUpper78
import BandRowsUpper90
import BandRowsUpper101
import BandRowsUpper112
import BandRowsUpper122
import BandRowsUpper131
import BandRowsUpper139
import BandRowsUpper147
import BandRowsUpper154
import BandRowsUpper161
import BandRowsUpper167
import BandRowsUpper172
import BandRowsUpper177
import BandRowsUpper182
import BandRowsUpper186
import BandRowsUpper190
import BandRowsUpper194
import BandRowsUpper198
import BandRowsUpper201
import BandRowsUpper204
import BandRowsUpper207
import BandRowsUpper209
import BandRowsUpper211
import BandRowsUpper213
import BandRowsUpper215
import BandRowsUpper217
import BandRowsUpper218
import BandRowsUpper219
import BandRowsUpper220
import BandRowsUpper221
import BandRowsUpper222
import BandRowsUpper223
import BandRowsUpper224
import BandRowsUpper225
import BandRowsUpper226
import BandRowsUpper227
import BandRowsUpper228
import BandRowsUpper229
import BandRowsUpper230
import BandRowsUpper231
import BandRowsUpper232
import BandRowsUpper233
import BandRowsUpper234
import BandRowsUpper235
import BandRowsUpper236
import BandVerifiedCacheValidity
import BandVerifiedCacheProof2

namespace GaussianChains.Band.Material

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem upperOfValid (V : Fast.Valid .upper (Fast.packetCache .upper))
    (b : Fin Slab.upper.count) (i : Fin 18) : RowExcluded .upper b i := by
  fin_cases b
  · exact floor2_0 V i
  · exact floor2_1 V i
  · exact floor2_2 V i
  · exact floor2_3 V i
  · exact floor2_4 V i
  · exact floor2_5 V i
  · exact floor2_6 V i
  · exact floor2_7 V i
  · exact floor2_8 V i
  · exact floor2_9 V i
  · exact floor2_10 V i
  · exact floor2_11 V i
  · exact floor2_12 V i
  · exact floor2_13 V i
  · exact floor2_14 V i
  · exact floor2_15 V i
  · exact floor2_16 V i
  · exact floor2_17 V i
  · exact floor2_18 V i
  · exact floor2_19 V i
  · exact floor2_20 V i
  · exact floor2_21 V i
  · exact floor2_22 V i
  · exact floor2_23 V i
  · exact floor2_24 V i
  · exact floor2_25 V i
  · exact floor2_26 V i
  · exact floor2_27 V i
  · exact floor2_28 V i
  · exact floor2_29 V i
  · exact floor2_30 V i
  · exact floor2_31 V i
  · exact floor2_32 V i
  · exact floor2_33 V i
  · exact floor2_34 V i
  · exact floor2_35 V i
  · exact floor2_36 V i
  · exact floor2_37 V i
  · exact floor2_38 V i
  · exact floor2_39 V i
  · exact floor2_40 V i
  · exact floor2_41 V i
  · exact floor2_42 V i
  · exact floor2_43 V i
  · exact floor2_44 V i
  · exact floor2_45 V i
  · exact floor2_46 V i
  · exact floor2_47 V i
  · exact floor2_48 V i

theorem upperChecked (b : Fin Slab.upper.count) (i : Fin 18) : RowExcluded .upper b i :=
  upperOfValid (Fast.packetCache_valid .upper Fast.checkedAnchor2) b i

#print axioms upperChecked
end GaussianChains.Band.Material
