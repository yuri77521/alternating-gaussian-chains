import BandRowsNarrow04

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node0_758 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 0) 17 4 (box 2048 9671701722837710838697984) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (by decide +kernel) (by decide +kernel) (node0_754 V) (node0_757 V)

theorem node0_759 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 0) 17 4 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node0_741 V) (node0_758 V)

theorem safe0_0_17 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 0) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_759 V)

theorem floor0_0 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) (i : Fin 18) : RowExcluded .narrow (floorId .narrow 0) i := by
  fin_cases i
  · exact safe0_0_0 V
  · exact safe0_0_1 V
  · exact safe0_0_2 V
  · exact safe0_0_3 V
  · exact safe0_0_4 V
  · exact safe0_0_5 V
  · exact safe0_0_6 V
  · exact safe0_0_7 V
  · exact safe0_0_8 V
  · exact safe0_0_9 V
  · exact safe0_0_10 V
  · exact safe0_0_11 V
  · exact safe0_0_12 V
  · exact safe0_0_13 V
  · exact safe0_0_14 V
  · exact safe0_0_15 V
  · exact safe0_0_16 V
  · exact safe0_0_17 V


end GaussianChains.Band.Material
