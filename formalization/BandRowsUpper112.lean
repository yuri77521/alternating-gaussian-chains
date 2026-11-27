import BandRowsUpper111

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node2_20491 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 7) 17 4 (box 2417851639229258382968832 4835850861418855436127232) :=
  nodeSafe_split 2 1024 (by decide +kernel : checkChamber (box 2417851639229258382968832 4835850861418855436127232) (stage 2417851639229258382968832 4835850861418855436127232 2417851639229258382968832 4835850861418855436127232) (stage 2417851639229258382968832 4835850861418855436127232 2417851639229258382968832 4835850861418855436127232) = true) (by decide +kernel) (by decide +kernel) (node2_20489 V) (node2_20490 V)

theorem node2_20492 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 7) 17 4 (box 2417851639229258399746048 4835850861418855452904448) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258399746048 4835850861418855452904448) (stage 2417851639229258399746048 3626851250324056934714368 3626777458843887574452224 3626851250324056917937152) (stage 3626777458843887574452224 3626777458843887574452224 3626777458843887574452224 3626777458843887574452224) = true) (.transfer (.gradient 0)) (by decide +kernel)

theorem node2_20493 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 7) 17 4 (box 2417851639229258382968832 4835850861418855452904448) :=
  nodeSafe_split 1 3072 (by decide +kernel : checkChamber (box 2417851639229258382968832 4835850861418855452904448) (stage 2417851639229258382968832 4835850861418855452904448 2417851639229258382968832 4835850861418855452904448) (stage 2417851639229258382968832 4835850861418855452904448 2417851639229258382968832 4835850861418855452904448) = true) (by decide +kernel) (by decide +kernel) (node2_20491 V) (node2_20492 V)

theorem node2_20494 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 7) 17 4 (box 2417851639229258382969856 4835850861418855452905472) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258382969856 4835850861418855452905472) (stage 2417851639229258382969856 3626851250324056917938176 3626777458843887557676032 3626851250324056917937152) (stage 3626777458843887557676032 3626777458843887557676032 3626777458843887557676032 3626777458843887557676032) = true) (.transfer (.gradient 0)) (by decide +kernel)

theorem node2_20495 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 7) 17 4 (box 2417851639229258382968832 7253850083608452489285632) :=
  nodeSafe_split 0 3072 (by decide +kernel : checkChamber (box 2417851639229258382968832 7253850083608452489285632) (stage 2417851639229258382968832 4835850861418855452905472 2417851639229258382968832 4835850861418855452905472) (stage 2417851639229258382968832 4835850861418855452905472 2417851639229258382968832 4835850861418855452905472) = true) (by decide +kernel) (by decide +kernel) (node2_20493 V) (node2_20494 V)

theorem node2_20496 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 7) 17 4 (box 2048 9671701722837710838697984) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (by decide +kernel) (by decide +kernel) (node2_20488 V) (node2_20495 V)

theorem node2_20497 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 7) 17 4 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node2_20465 V) (node2_20496 V)

theorem safe2_7_17 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 7) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_20497 V)

theorem floor2_7 (V : Fast.Valid .upper (Fast.packetCache .upper)) (i : Fin 18) : RowExcluded .upper (floorId .upper 7) i := by
  fin_cases i
  · exact safe2_7_0 V
  · exact safe2_7_1 V
  · exact safe2_7_2 V
  · exact safe2_7_3 V
  · exact safe2_7_4 V
  · exact safe2_7_5 V
  · exact safe2_7_6 V
  · exact safe2_7_7 V
  · exact safe2_7_8 V
  · exact safe2_7_9 V
  · exact safe2_7_10 V
  · exact safe2_7_11 V
  · exact safe2_7_12 V
  · exact safe2_7_13 V
  · exact safe2_7_14 V
  · exact safe2_7_15 V
  · exact safe2_7_16 V
  · exact safe2_7_17 V


end GaussianChains.Band.Material
