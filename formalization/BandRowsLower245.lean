import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node1_40722 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 0 4 (box 0 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_0 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40722 V)

theorem node1_40723 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 1 4 (box 0 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_48_1 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40723 V)

theorem node1_40724 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 2 4 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_2 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40724 V)

theorem node1_40725 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 3 4 (box 0 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_3 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40725 V)

theorem node1_40726 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 4 4 (box 0 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_4 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40726 V)

theorem node1_40727 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 5 4 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_5 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40727 V)

theorem node1_40728 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 6 4 (box 0 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_48_6 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40728 V)

theorem node1_40729 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 7 4 (box 0 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_48_7 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40729 V)

theorem node1_40730 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 8 4 (box 0 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_8 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40730 V)

theorem node1_40731 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 9 4 (box 0 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_9 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40731 V)

theorem node1_40732 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 10 4 (box 0 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_10 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40732 V)

theorem node1_40733 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 11 4 (box 0 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_11 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40733 V)

theorem node1_40734 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 12 4 (box 0 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_12 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40734 V)

theorem node1_40735 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 13 4 (box 0 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_48_13 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40735 V)

theorem node1_40736 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 14 4 (box 0 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_14 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40736 V)

theorem node1_40737 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 15 4 (box 0 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_15 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40737 V)

theorem node1_40738 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 16 4 (box 0 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_16 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40738 V)

theorem node1_40739 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 48) 17 4 (box 0 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe1_48_17 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 48) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40739 V)

theorem floor1_48 (V : Fast.Valid .lower (Fast.packetCache .lower)) (i : Fin 18) : RowExcluded .lower (floorId .lower 48) i := by
  fin_cases i
  · exact safe1_48_0 V
  · exact safe1_48_1 V
  · exact safe1_48_2 V
  · exact safe1_48_3 V
  · exact safe1_48_4 V
  · exact safe1_48_5 V
  · exact safe1_48_6 V
  · exact safe1_48_7 V
  · exact safe1_48_8 V
  · exact safe1_48_9 V
  · exact safe1_48_10 V
  · exact safe1_48_11 V
  · exact safe1_48_12 V
  · exact safe1_48_13 V
  · exact safe1_48_14 V
  · exact safe1_48_15 V
  · exact safe1_48_16 V
  · exact safe1_48_17 V


end GaussianChains.Band.Material
