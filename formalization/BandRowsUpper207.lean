import BandRowsUpper206

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node2_36810 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 16 4 (box 0 9671701722836611327070208) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (by decide +kernel) (by decide +kernel) (node2_36802 V) (node2_36809 V)

theorem safe2_24_16 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 24) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_36810 V)

theorem node2_36811 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671554139877372101395456) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671554139877372101395456) (stage 0 9671554139877372101395456 0 9671554139877372101395456) (stage 0 9671554139877372101395456 0 9671554139877372101395456) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_36812 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 16777216 9671554139877372118172672) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 16777216 9671554139877372118172672) (stage 16777216 8462628320262742943466496 1208925819614629191483392 8462628320262742943466496) (stage 1208925819614629191483392 8462628320262742943466496 1208925819614629191483392 8462628320262742943466496) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_36813 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671554139877372118172672) :=
  nodeSafe_split 1 1024 (by decide +kernel : checkChamber (box 0 9671554139877372118172672) (stage 0 9671554139877372118172672 0 9671554139877372118172672) (stage 0 9671554139877372118172672 0 9671554139877372118172672) = true) (by decide +kernel) (by decide +kernel) (node2_36811 V) (node2_36812 V)

theorem node2_36814 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 1024 9671554139877372118173696) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 1024 9671554139877372118173696) (stage 1024 8462628320262742943467520 1208925819614629174707200 8462628320262742943467520) (stage 1208925819614629174707200 8462628320262742943467520 1208925819614629174707200 8462628320262742943467520) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_36815 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671554139877372118173696) :=
  nodeSafe_split 0 1024 (by decide +kernel : checkChamber (box 0 9671554139877372118173696) (stage 0 9671554139877372118173696 0 9671554139877372118173696) (stage 0 9671554139877372118173696 0 9671554139877372118173696) = true) (by decide +kernel) (by decide +kernel) (node2_36813 V) (node2_36814 V)

theorem node2_36816 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 147573952589676412928 9671701713829961794586624) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 147573952589676412928 9671701713829961794586624) (stage 147573952589676412928 7253850074600703445174272 2417999213181848025825280 7253850074600703445174272) (stage 2417999213181848025825280 7253850074600703445174272 2417999213181848025825280 7253850074600703445174272) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_36817 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671701713829961794586624) :=
  nodeSafe_split 4 2048 (by decide +kernel : checkChamber (box 0 9671701713829961794586624) (stage 0 9671701713829961794586624 0 9671701713829961794586624) (stage 0 9671701713829961794586624 0 9671701713829961794586624) = true) (by decide +kernel) (by decide +kernel) (node2_36815 V) (node2_36816 V)

theorem node2_36818 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 9007199254740992 9671701722837161049327616) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 9007199254740992 9671701722837161049327616) (stage 9007199254740992 7253850083607902699915264 2417851648236457604153344 7253850083607902699915264) (stage 2417851648236457604153344 7253850083607902699915264 2417851648236457604153344 7253850083607902699915264) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_36819 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671701722837161049327616) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671701722837161049327616) (stage 0 9671701722837161049327616 0 9671701722837161049327616) (stage 0 9671701722837161049327616 0 9671701722837161049327616) = true) (by decide +kernel) (by decide +kernel) (node2_36817 V) (node2_36818 V)

theorem node2_36820 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 549755813888 9671701722837710805141504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 549755813888 9671701722837710805141504) (stage 549755813888 7253850083608452455729152 2417851639229808105226240 7253850083608452455729152) (stage 2417851639229808105226240 7253850083608452455729152 2417851639229808105226240 7253850083608452455729152) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_36821 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671701722837710805141504) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 0 9671701722837710805141504) (stage 0 9671701722837710805141504 0 9671701722837710805141504) (stage 0 9671701722837710805141504 0 9671701722837710805141504) = true) (by decide +kernel) (by decide +kernel) (node2_36819 V) (node2_36820 V)

theorem node2_36822 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 33554432 9671701722837710838695936) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671701722837710838695936) (stage 33554432 7253850083608452489283584 2417851639229258382966784 7253850083608452489283584) (stage 2417851639229258382966784 7253850083608452489283584 2417851639229258382966784 7253850083608452489283584) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_36823 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671701722837710838695936) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) = true) (by decide +kernel) (by decide +kernel) (node2_36821 V) (node2_36822 V)

theorem node2_36824 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 2417851639229258349414400 7253850083607902699917312) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349414400 7253850083607902699917312) (stage 2417851639229258349414400 7253850083607902699917312 2417851639229258349414400 7253850083607902699917312) (stage 2417851639229258349414400 7253850083607902699917312 2417851639229258349414400 7253850083607902699917312) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node2_36825 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 2417851639229808105228288 7253850083608452455731200) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229808105228288 7253850083608452455731200) (stage 2417851639229808105228288 4835850861419405175164928 2417851639229808105228288 4835850861419405175164928) (stage 2417851639229808105228288 4835850861419405175164928 2417851639229808105228288 4835850861419405175164928) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_36826 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 2417851639229258349414400 7253850083608452455731200) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 2417851639229258349414400 7253850083608452455731200) (stage 2417851639229258349414400 7253850083608452455731200 2417851639229258349414400 7253850083608452455731200) (stage 2417851639229258349414400 7253850083608452455731200 2417851639229258349414400 7253850083608452455731200) = true) (by decide +kernel) (by decide +kernel) (node2_36824 V) (node2_36825 V)

theorem node2_36827 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 2417851639229258382968832 7253850083608452489285632) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258382968832 7253850083608452489285632) (stage 2417851639229258382968832 4835850861418855452905472 2417851639229258382968832 4835850861418855452905472) (stage 2417851639229258382968832 4835850861418855452905472 2417851639229258382968832 4835850861418855452905472) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_36828 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 2048 9671701722837710838697984) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (by decide +kernel) (by decide +kernel) (node2_36826 V) (node2_36827 V)

theorem node2_36829 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 24) 17 4 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node2_36823 V) (node2_36828 V)

theorem safe2_24_17 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 24) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_36829 V)

theorem floor2_24 (V : Fast.Valid .upper (Fast.packetCache .upper)) (i : Fin 18) : RowExcluded .upper (floorId .upper 24) i := by
  fin_cases i
  · exact safe2_24_0 V
  · exact safe2_24_1 V
  · exact safe2_24_2 V
  · exact safe2_24_3 V
  · exact safe2_24_4 V
  · exact safe2_24_5 V
  · exact safe2_24_6 V
  · exact safe2_24_7 V
  · exact safe2_24_8 V
  · exact safe2_24_9 V
  · exact safe2_24_10 V
  · exact safe2_24_11 V
  · exact safe2_24_12 V
  · exact safe2_24_13 V
  · exact safe2_24_14 V
  · exact safe2_24_15 V
  · exact safe2_24_16 V
  · exact safe2_24_17 V


end GaussianChains.Band.Material
