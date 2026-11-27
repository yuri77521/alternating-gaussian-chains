import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node0_6050 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 0 4 (box 0 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_0 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6050 V)

theorem node0_6051 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 1 4 (box 0 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe0_13_1 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6051 V)

theorem node0_6052 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 2 4 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_2 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6052 V)

theorem node0_6053 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 3 4 (box 0 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_3 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6053 V)

theorem node0_6054 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 4 4 (box 0 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_4 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6054 V)

theorem node0_6055 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 5 4 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_5 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6055 V)

theorem node0_6056 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 6 4 (box 0 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem safe0_13_6 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6056 V)

theorem node0_6057 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 7 4 (box 0 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (.transfer (.curvature 1 3)) (by decide +kernel)

theorem safe0_13_7 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6057 V)

theorem node0_6058 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 8 4 (box 0 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_8 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6058 V)

theorem node0_6059 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 9 4 (box 0 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_9 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6059 V)

theorem node0_6060 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 10 4 (box 0 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_10 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6060 V)

theorem node0_6061 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 11 4 (box 0 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_11 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6061 V)

theorem node0_6062 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 12 4 (box 0 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_12 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6062 V)

theorem node0_6063 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 13 4 (box 0 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem safe0_13_13 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6063 V)

theorem node0_6064 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 14 4 (box 0 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_14 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6064 V)

theorem node0_6065 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 15 4 (box 0 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_15 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6065 V)

theorem node0_6066 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 16 4 (box 0 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_16 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6066 V)

theorem node0_6067 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 13) 17 4 (box 0 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe0_13_17 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 13) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6067 V)

theorem floor0_13 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) (i : Fin 18) : RowExcluded .narrow (floorId .narrow 13) i := by
  fin_cases i
  · exact safe0_13_0 V
  · exact safe0_13_1 V
  · exact safe0_13_2 V
  · exact safe0_13_3 V
  · exact safe0_13_4 V
  · exact safe0_13_5 V
  · exact safe0_13_6 V
  · exact safe0_13_7 V
  · exact safe0_13_8 V
  · exact safe0_13_9 V
  · exact safe0_13_10 V
  · exact safe0_13_11 V
  · exact safe0_13_12 V
  · exact safe0_13_13 V
  · exact safe0_13_14 V
  · exact safe0_13_15 V
  · exact safe0_13_16 V
  · exact safe0_13_17 V


end GaussianChains.Band.Material
