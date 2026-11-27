import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node1_40532 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 0 0 (box 4835703278458516698824704 9671406556917033397651456) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40533 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 0 0 (box 4835703278458516698826752 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698826752 9671406556917033397653504) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40534 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 0 0 (box 0 9671406556917033397653504) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (by decide +kernel) (by decide +kernel) (node1_40532 V) (node1_40533 V)

theorem safe1_38_0 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40534 V)

theorem node1_40535 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 1 0 (box 0 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem safe1_38_1 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40535 V)

theorem node1_40536 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 2 0 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_2 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40536 V)

theorem node1_40537 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 3 0 (box 0 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem safe1_38_3 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40537 V)

theorem node1_40538 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 4 0 (box 0 9671406574931431907133440) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40539 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 4 0 (box 2048 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431907135488) (stage 2048 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) (stage 2417851639229258349414400 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40540 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 4 0 (box 0 9671406574931431907135488) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (by decide +kernel) (by decide +kernel) (node1_40538 V) (node1_40539 V)

theorem safe1_38_4 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40540 V)

theorem node1_40541 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 5 0 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem safe1_38_5 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40541 V)

theorem node1_40542 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 6 0 (box 0 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem safe1_38_6 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40542 V)

theorem node1_40543 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 7 0 (box 0 9671406574931431940685824) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) = true) (.transfer (.curvature 1 3)) (by decide +kernel)

theorem node1_40544 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 7 0 (box 33554432 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406574931431974240256) (stage 33554432 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) (stage 2417851639229258382966784 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node1_40545 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 7 0 (box 0 9671406574931431974240256) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (by decide +kernel) (by decide +kernel) (node1_40543 V) (node1_40544 V)

theorem safe1_38_7 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40545 V)

theorem node1_40546 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 8 0 (box 0 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_8 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40546 V)

theorem node1_40547 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 9 0 (box 0 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_9 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40547 V)

theorem node1_40548 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 10 0 (box 0 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_10 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40548 V)

theorem node1_40549 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 11 0 (box 0 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (.transfer (.curvature 2 3)) (by decide +kernel)

theorem safe1_38_11 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40549 V)

theorem node1_40550 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 12 0 (box 0 9671701704823312262105088) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40551 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 12 0 (box 2048 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312262107136) (stage 2048 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) (stage 2417851639229258349414400 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40552 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 12 0 (box 0 9671701704823312262107136) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (by decide +kernel) (by decide +kernel) (node1_40550 V) (node1_40551 V)

theorem safe1_38_12 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40552 V)

theorem node1_40553 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 13 0 (box 0 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem safe1_38_13 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40553 V)

theorem node1_40554 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 14 0 (box 0 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_14 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40554 V)

theorem node1_40555 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 15 0 (box 0 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_15 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40555 V)

theorem node1_40556 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 16 0 (box 0 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_16 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40556 V)

theorem node1_40557 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 38) 17 0 (box 0 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_38_17 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 38) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40557 V)

theorem floor1_38 (V : Fast.Valid .lower (Fast.packetCache .lower)) (i : Fin 18) : RowExcluded .lower (floorId .lower 38) i := by
  fin_cases i
  · exact safe1_38_0 V
  · exact safe1_38_1 V
  · exact safe1_38_2 V
  · exact safe1_38_3 V
  · exact safe1_38_4 V
  · exact safe1_38_5 V
  · exact safe1_38_6 V
  · exact safe1_38_7 V
  · exact safe1_38_8 V
  · exact safe1_38_9 V
  · exact safe1_38_10 V
  · exact safe1_38_11 V
  · exact safe1_38_12 V
  · exact safe1_38_13 V
  · exact safe1_38_14 V
  · exact safe1_38_15 V
  · exact safe1_38_16 V
  · exact safe1_38_17 V


end GaussianChains.Band.Material
