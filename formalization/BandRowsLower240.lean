import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node1_40632 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 0 0 (box 0 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_0 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40632 V)

theorem node1_40633 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 1 0 (box 0 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_43_1 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40633 V)

theorem node1_40634 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 2 0 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_2 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40634 V)

theorem node1_40635 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 3 0 (box 0 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_3 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40635 V)

theorem node1_40636 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 4 0 (box 0 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_4 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40636 V)

theorem node1_40637 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 5 0 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_5 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40637 V)

theorem node1_40638 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 6 0 (box 0 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_43_6 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40638 V)

theorem node1_40639 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 7 0 (box 0 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_43_7 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40639 V)

theorem node1_40640 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 8 0 (box 0 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_8 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40640 V)

theorem node1_40641 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 9 0 (box 0 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_9 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40641 V)

theorem node1_40642 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 10 0 (box 0 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_10 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40642 V)

theorem node1_40643 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 11 0 (box 0 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_11 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40643 V)

theorem node1_40644 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 12 0 (box 0 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_12 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40644 V)

theorem node1_40645 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 13 0 (box 0 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_43_13 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40645 V)

theorem node1_40646 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 14 0 (box 0 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_14 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40646 V)

theorem node1_40647 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 15 0 (box 0 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_15 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40647 V)

theorem node1_40648 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 16 0 (box 0 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_16 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40648 V)

theorem node1_40649 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 43) 17 0 (box 0 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_43_17 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 43) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40649 V)

theorem floor1_43 (V : Fast.Valid .lower (Fast.packetCache .lower)) (i : Fin 18) : RowExcluded .lower (floorId .lower 43) i := by
  fin_cases i
  · exact safe1_43_0 V
  · exact safe1_43_1 V
  · exact safe1_43_2 V
  · exact safe1_43_3 V
  · exact safe1_43_4 V
  · exact safe1_43_5 V
  · exact safe1_43_6 V
  · exact safe1_43_7 V
  · exact safe1_43_8 V
  · exact safe1_43_9 V
  · exact safe1_43_10 V
  · exact safe1_43_11 V
  · exact safe1_43_12 V
  · exact safe1_43_13 V
  · exact safe1_43_14 V
  · exact safe1_43_15 V
  · exact safe1_43_16 V
  · exact safe1_43_17 V


end GaussianChains.Band.Material
