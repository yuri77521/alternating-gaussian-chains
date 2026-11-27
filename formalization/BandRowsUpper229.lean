import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node2_38912 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 0 0 (box 0 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_0 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38912 V)

theorem node2_38913 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 1 0 (box 0 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_41_1 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38913 V)

theorem node2_38914 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 2 0 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_2 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38914 V)

theorem node2_38915 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 3 0 (box 0 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_3 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38915 V)

theorem node2_38916 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 4 0 (box 0 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_4 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38916 V)

theorem node2_38917 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 5 0 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_5 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38917 V)

theorem node2_38918 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 6 0 (box 0 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_41_6 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38918 V)

theorem node2_38919 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 7 0 (box 0 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_41_7 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38919 V)

theorem node2_38920 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 8 0 (box 0 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_8 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38920 V)

theorem node2_38921 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 9 0 (box 0 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_9 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38921 V)

theorem node2_38922 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 10 0 (box 0 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_10 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38922 V)

theorem node2_38923 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 11 0 (box 0 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_11 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38923 V)

theorem node2_38924 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 12 0 (box 0 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_12 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38924 V)

theorem node2_38925 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 13 0 (box 0 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe2_41_13 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38925 V)

theorem node2_38926 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 14 0 (box 0 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_14 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38926 V)

theorem node2_38927 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 15 0 (box 0 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_15 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38927 V)

theorem node2_38928 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 16 0 (box 0 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_16 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38928 V)

theorem node2_38929 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 41) 17 0 (box 0 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem safe2_41_17 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 41) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38929 V)

theorem floor2_41 (V : Fast.Valid .upper (Fast.packetCache .upper)) (i : Fin 18) : RowExcluded .upper (floorId .upper 41) i := by
  fin_cases i
  · exact safe2_41_0 V
  · exact safe2_41_1 V
  · exact safe2_41_2 V
  · exact safe2_41_3 V
  · exact safe2_41_4 V
  · exact safe2_41_5 V
  · exact safe2_41_6 V
  · exact safe2_41_7 V
  · exact safe2_41_8 V
  · exact safe2_41_9 V
  · exact safe2_41_10 V
  · exact safe2_41_11 V
  · exact safe2_41_12 V
  · exact safe2_41_13 V
  · exact safe2_41_14 V
  · exact safe2_41_15 V
  · exact safe2_41_16 V
  · exact safe2_41_17 V


end GaussianChains.Band.Material
