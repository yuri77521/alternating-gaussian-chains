import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node2_38966 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 0 0 (box 0 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_0 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38966 V)

theorem node2_38967 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 1 0 (box 0 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_44_1 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38967 V)

theorem node2_38968 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 2 0 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_2 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38968 V)

theorem node2_38969 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 3 0 (box 0 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_3 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38969 V)

theorem node2_38970 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 4 0 (box 0 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_4 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38970 V)

theorem node2_38971 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 5 0 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_5 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38971 V)

theorem node2_38972 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 6 0 (box 0 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_44_6 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38972 V)

theorem node2_38973 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 7 0 (box 0 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_44_7 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38973 V)

theorem node2_38974 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 8 0 (box 0 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_8 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38974 V)

theorem node2_38975 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 9 0 (box 0 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_9 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38975 V)

theorem node2_38976 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 10 0 (box 0 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_10 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38976 V)

theorem node2_38977 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 11 0 (box 0 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_11 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38977 V)

theorem node2_38978 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 12 0 (box 0 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_12 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38978 V)

theorem node2_38979 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 13 0 (box 0 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_44_13 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38979 V)

theorem node2_38980 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 14 0 (box 0 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_14 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38980 V)

theorem node2_38981 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 15 0 (box 0 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_15 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38981 V)

theorem node2_38982 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 16 0 (box 0 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_16 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38982 V)

theorem node2_38983 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 44) 17 0 (box 0 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_44_17 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 44) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38983 V)

theorem floor2_44 (V : Fast.Valid .upper (Fast.packetCache .upper)) (i : Fin 18) : RowExcluded .upper (floorId .upper 44) i := by
  fin_cases i
  · exact safe2_44_0 V
  · exact safe2_44_1 V
  · exact safe2_44_2 V
  · exact safe2_44_3 V
  · exact safe2_44_4 V
  · exact safe2_44_5 V
  · exact safe2_44_6 V
  · exact safe2_44_7 V
  · exact safe2_44_8 V
  · exact safe2_44_9 V
  · exact safe2_44_10 V
  · exact safe2_44_11 V
  · exact safe2_44_12 V
  · exact safe2_44_13 V
  · exact safe2_44_14 V
  · exact safe2_44_15 V
  · exact safe2_44_16 V
  · exact safe2_44_17 V


end GaussianChains.Band.Material
