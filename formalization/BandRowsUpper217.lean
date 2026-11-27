import BandRowsUpper216

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node2_38118 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 29) 17 1 (box 33554432 9671701722837710838695936) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671701722837710838695936) (stage 33554432 7253850083608452489283584 2417851639229258382966784 7253850083608452489283584) (stage 2417851639229258382966784 7253850083608452489283584 2417851639229258382966784 7253850083608452489283584) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38119 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 29) 17 1 (box 0 9671701722837710838695936) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) = true) (by decide +kernel) (by decide +kernel) (node2_38117 V) (node2_38118 V)

theorem node2_38120 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 29) 17 1 (box 2417851639229258349414400 7253850083608452455731200) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349414400 7253850083608452455731200) (stage 2417851639229258349414400 7253850083608452455731200 2417851639229258349414400 7253850083608452455731200) (stage 2417851639229258349414400 7253850083608452455731200 2417851639229258349414400 7253850083608452455731200) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38121 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 29) 17 1 (box 2417851639229258382968832 7253850083608452489285632) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258382968832 7253850083608452489285632) (stage 2417851639229258382968832 4835850861418855452905472 2417851639229258382968832 4835850861418855452905472) (stage 2417851639229258382968832 4835850861418855452905472 2417851639229258382968832 4835850861418855452905472) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38122 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 29) 17 1 (box 2048 9671701722837710838697984) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (by decide +kernel) (by decide +kernel) (node2_38120 V) (node2_38121 V)

theorem node2_38123 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 29) 17 1 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node2_38119 V) (node2_38122 V)

theorem safe2_29_17 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 29) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38123 V)

theorem floor2_29 (V : Fast.Valid .upper (Fast.packetCache .upper)) (i : Fin 18) : RowExcluded .upper (floorId .upper 29) i := by
  fin_cases i
  · exact safe2_29_0 V
  · exact safe2_29_1 V
  · exact safe2_29_2 V
  · exact safe2_29_3 V
  · exact safe2_29_4 V
  · exact safe2_29_5 V
  · exact safe2_29_6 V
  · exact safe2_29_7 V
  · exact safe2_29_8 V
  · exact safe2_29_9 V
  · exact safe2_29_10 V
  · exact safe2_29_11 V
  · exact safe2_29_12 V
  · exact safe2_29_13 V
  · exact safe2_29_14 V
  · exact safe2_29_15 V
  · exact safe2_29_16 V
  · exact safe2_29_17 V


end GaussianChains.Band.Material
