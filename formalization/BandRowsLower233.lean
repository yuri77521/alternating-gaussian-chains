import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node1_40422 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 0 0 (box 4835703278458516698824704 9671406556917033397651456) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40423 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 0 0 (box 4835703278458516698826752 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698826752 9671406556917033397653504) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40424 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 0 0 (box 0 9671406556917033397653504) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (by decide +kernel) (by decide +kernel) (node1_40422 V) (node1_40423 V)

theorem safe1_36_0 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40424 V)

theorem node1_40425 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 1 0 (box 4835703278458516698824704 9671406556917033431203840) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node1_40426 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 1 0 (box 4835703278458516732379136 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516732379136 9671406556917033464758272) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node1_40427 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 1 0 (box 0 9671406556917033464758272) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (by decide +kernel) (by decide +kernel) (node1_40425 V) (node1_40426 V)

theorem safe1_36_1 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40427 V)

theorem node1_40428 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 2 0 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe1_36_2 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40428 V)

theorem node1_40429 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 3 0 (box 0 9671406556918132909279232) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node1_40430 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 3 0 (box 2048 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406556918132909281280) (stage 2048 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) (stage 2417851639229258349414400 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40431 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 3 0 (box 0 9671406556918132909281280) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (by decide +kernel) (by decide +kernel) (node1_40429 V) (node1_40430 V)

theorem safe1_36_3 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40431 V)

theorem node1_40432 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 4 0 (box 2417851639229258349412352 9671406565924232652392448) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40433 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 4 0 (box 2417851648236457604153344 9671406574931431907133440) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431907133440) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40434 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 4 0 (box 0 9671406574931431907133440) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) = true) (by decide +kernel) (by decide +kernel) (node1_40432 V) (node1_40433 V)

theorem node1_40435 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 4 0 (box 2048 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431907135488) (stage 2048 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) (stage 2417851639229258349414400 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40436 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 4 0 (box 0 9671406574931431907135488) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (by decide +kernel) (by decide +kernel) (node1_40434 V) (node1_40435 V)

theorem safe1_36_4 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40436 V)

theorem node1_40437 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 5 0 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem safe1_36_5 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40437 V)

theorem node1_40438 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 6 0 (box 0 9671406556918132942831616) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node1_40439 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 6 0 (box 33554432 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406556918132976386048) (stage 33554432 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) (stage 2417851639229258382966784 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node1_40440 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 6 0 (box 0 9671406556918132976386048) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (by decide +kernel) (by decide +kernel) (node1_40438 V) (node1_40439 V)

theorem safe1_36_6 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40440 V)

theorem node1_40441 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 7 0 (box 2417851639229258349412352 9671406565924232685944832) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node1_40442 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 7 0 (box 2417851648236457604153344 9671406574931431940685824) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431940685824) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) = true) (.transfer (.curvature 3 5)) (by decide +kernel)

theorem node1_40443 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 7 0 (box 0 9671406574931431940685824) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) = true) (by decide +kernel) (by decide +kernel) (node1_40441 V) (node1_40442 V)

theorem node1_40444 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 7 0 (box 33554432 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406574931431974240256) (stage 33554432 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) (stage 2417851639229258382966784 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node1_40445 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 7 0 (box 0 9671406574931431974240256) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (by decide +kernel) (by decide +kernel) (node1_40443 V) (node1_40444 V)

theorem safe1_36_7 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40445 V)

theorem node1_40446 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 8 0 (box 0 9671406556918132976388096) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node1_40447 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 8 0 (box 2048 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406556918132976390144) (stage 2048 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) (stage 2417851639229258349414400 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40448 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 8 0 (box 0 9671406556918132976390144) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (by decide +kernel) (by decide +kernel) (node1_40446 V) (node1_40447 V)

theorem safe1_36_8 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40448 V)

theorem node1_40449 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 9 0 (box 0 9671406574931431974242304) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node1_40450 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 9 0 (box 2048 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431974244352) (stage 2048 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) (stage 2417851639229258349414400 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40451 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 9 0 (box 0 9671406574931431974244352) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (by decide +kernel) (by decide +kernel) (node1_40449 V) (node1_40450 V)

theorem safe1_36_9 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40451 V)

theorem node1_40452 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 10 0 (box 0 9671701704822212817586176) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node1_40453 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 10 0 (box 2048 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704822212817588224) (stage 2048 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) (stage 2417851639229258349414400 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40454 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 10 0 (box 0 9671701704822212817588224) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (by decide +kernel) (by decide +kernel) (node1_40452 V) (node1_40453 V)

theorem safe1_36_10 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40454 V)

theorem node1_40455 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 11 0 (box 0 9671406574931981662947328) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node1_40456 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 11 0 (box 549755813888 9671406574932531418761216) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 549755813888 9671406574932531418761216) (stage 549755813888 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) (stage 2417851639229808105226240 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40457 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 11 0 (box 0 9671406574932531418761216) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) = true) (by decide +kernel) (by decide +kernel) (node1_40455 V) (node1_40456 V)

theorem node1_40458 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 11 0 (box 2048 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574932531418763264) (stage 2048 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) (stage 2417851639229258349414400 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40459 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 11 0 (box 0 9671406574932531418763264) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (by decide +kernel) (by decide +kernel) (node1_40457 V) (node1_40458 V)

theorem safe1_36_11 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40459 V)

theorem node1_40460 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 12 0 (box 0 9671701704823312262105088) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem node1_40461 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 12 0 (box 2048 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312262107136) (stage 2048 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) (stage 2417851639229258349414400 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40462 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 12 0 (box 0 9671701704823312262107136) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (by decide +kernel) (by decide +kernel) (node1_40460 V) (node1_40461 V)

theorem safe1_36_12 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40462 V)

theorem node1_40463 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 13 0 (box 0 9671406574932531452313600) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node1_40464 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 13 0 (box 33554432 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406574932531485868032) (stage 33554432 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) (stage 2417851639229258382966784 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node1_40465 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 13 0 (box 0 9671406574932531485868032) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (by decide +kernel) (by decide +kernel) (node1_40463 V) (node1_40464 V)

theorem safe1_36_13 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40465 V)

theorem node1_40466 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 14 0 (box 0 9671406574932531485870080) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node1_40467 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 14 0 (box 2048 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574932531485872128) (stage 2048 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) (stage 2417851639229258349414400 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40468 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 14 0 (box 0 9671406574932531485872128) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (by decide +kernel) (by decide +kernel) (node1_40466 V) (node1_40467 V)

theorem safe1_36_14 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40468 V)

theorem node1_40469 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 15 0 (box 0 9671701704823312329213952) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node1_40470 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 15 0 (box 2048 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312329216000) (stage 2048 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) (stage 2417851639229258349414400 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40471 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 15 0 (box 0 9671701704823312329216000) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (by decide +kernel) (by decide +kernel) (node1_40469 V) (node1_40470 V)

theorem safe1_36_15 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40471 V)

theorem node1_40472 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 16 0 (box 0 9671701722836611327068160) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node1_40473 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 16 0 (box 2048 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722836611327070208) (stage 2048 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) (stage 2417851639229258349414400 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40474 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 16 0 (box 0 9671701722836611327070208) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (by decide +kernel) (by decide +kernel) (node1_40472 V) (node1_40473 V)

theorem safe1_36_16 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40474 V)

theorem node1_40475 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 17 0 (box 0 9671701722837710838695936) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node1_40476 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 17 0 (box 2048 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node1_40477 (V : Fast.Valid .lower (Fast.packetCache .lower)) : NodeSafe .lower (floorId .lower 36) 17 0 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node1_40475 V) (node1_40476 V)

theorem safe1_36_17 (V : Fast.Valid .lower (Fast.packetCache .lower)) : RowExcluded .lower (floorId .lower 36) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node1_40477 V)

theorem floor1_36 (V : Fast.Valid .lower (Fast.packetCache .lower)) (i : Fin 18) : RowExcluded .lower (floorId .lower 36) i := by
  fin_cases i
  · exact safe1_36_0 V
  · exact safe1_36_1 V
  · exact safe1_36_2 V
  · exact safe1_36_3 V
  · exact safe1_36_4 V
  · exact safe1_36_5 V
  · exact safe1_36_6 V
  · exact safe1_36_7 V
  · exact safe1_36_8 V
  · exact safe1_36_9 V
  · exact safe1_36_10 V
  · exact safe1_36_11 V
  · exact safe1_36_12 V
  · exact safe1_36_13 V
  · exact safe1_36_14 V
  · exact safe1_36_15 V
  · exact safe1_36_16 V
  · exact safe1_36_17 V


end GaussianChains.Band.Material
