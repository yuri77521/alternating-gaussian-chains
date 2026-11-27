import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node0_5992 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 0 4 (box 4835703278458516698824704 9671406556917033397651456) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_5993 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 0 4 (box 4835703278458516698826752 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698826752 9671406556917033397653504) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_5994 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 0 4 (box 0 9671406556917033397653504) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (by decide +kernel) (by decide +kernel) (node0_5992 V) (node0_5993 V)

theorem safe0_12_0 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_5994 V)

theorem node0_5995 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 1 4 (box 4835703278458516698824704 9671406556917033431203840) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node0_5996 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 1 4 (box 4835703278458516732379136 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516732379136 9671406556917033464758272) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node0_5997 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 1 4 (box 0 9671406556917033464758272) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (by decide +kernel) (by decide +kernel) (node0_5995 V) (node0_5996 V)

theorem safe0_12_1 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_5997 V)

theorem node0_5998 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 2 4 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe0_12_2 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_5998 V)

theorem node0_5999 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 3 4 (box 0 9671406556918132909279232) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node0_6000 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 3 4 (box 2048 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406556918132909281280) (stage 2048 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) (stage 2417851639229258349414400 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6001 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 3 4 (box 0 9671406556918132909281280) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (by decide +kernel) (by decide +kernel) (node0_5999 V) (node0_6000 V)

theorem safe0_12_3 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6001 V)

theorem node0_6002 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 4 4 (box 2417851639229258349412352 9671406565924232652392448) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) = true) (.transfer (.curvature 3 5)) (by decide +kernel)

theorem node0_6003 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 4 4 (box 2417851648236457604153344 9671406574931431907133440) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431907133440) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6004 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 4 4 (box 0 9671406574931431907133440) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) = true) (by decide +kernel) (by decide +kernel) (node0_6002 V) (node0_6003 V)

theorem node0_6005 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 4 4 (box 2048 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431907135488) (stage 2048 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) (stage 2417851639229258349414400 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6006 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 4 4 (box 0 9671406574931431907135488) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (by decide +kernel) (by decide +kernel) (node0_6004 V) (node0_6005 V)

theorem safe0_12_4 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6006 V)

theorem node0_6007 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 5 4 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem safe0_12_5 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6007 V)

theorem node0_6008 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 6 4 (box 0 9671406556918132942831616) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node0_6009 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 6 4 (box 33554432 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406556918132976386048) (stage 33554432 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) (stage 2417851639229258382966784 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node0_6010 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 6 4 (box 0 9671406556918132976386048) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (by decide +kernel) (by decide +kernel) (node0_6008 V) (node0_6009 V)

theorem safe0_12_6 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6010 V)

theorem node0_6011 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 7 4 (box 2417851639229258349412352 9671406565924232685944832) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) = true) (.transfer (.curvature 1 3)) (by decide +kernel)

theorem node0_6012 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 7 4 (box 2417851648236457604153344 9671406574931431940685824) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431940685824) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) = true) (.transfer (.curvature 3 5)) (by decide +kernel)

theorem node0_6013 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 7 4 (box 0 9671406574931431940685824) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) = true) (by decide +kernel) (by decide +kernel) (node0_6011 V) (node0_6012 V)

theorem node0_6014 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 7 4 (box 33554432 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406574931431974240256) (stage 33554432 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) (stage 2417851639229258382966784 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node0_6015 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 7 4 (box 0 9671406574931431974240256) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (by decide +kernel) (by decide +kernel) (node0_6013 V) (node0_6014 V)

theorem safe0_12_7 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6015 V)

theorem node0_6016 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 8 4 (box 0 9671406556918132976388096) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node0_6017 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 8 4 (box 2048 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406556918132976390144) (stage 2048 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) (stage 2417851639229258349414400 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6018 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 8 4 (box 0 9671406556918132976390144) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (by decide +kernel) (by decide +kernel) (node0_6016 V) (node0_6017 V)

theorem safe0_12_8 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6018 V)

theorem node0_6019 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 9 4 (box 0 9671406574931431974242304) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node0_6020 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 9 4 (box 2048 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431974244352) (stage 2048 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) (stage 2417851639229258349414400 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6021 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 9 4 (box 0 9671406574931431974244352) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (by decide +kernel) (by decide +kernel) (node0_6019 V) (node0_6020 V)

theorem safe0_12_9 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6021 V)

theorem node0_6022 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 10 4 (box 0 9671701704822212817586176) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node0_6023 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 10 4 (box 2048 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704822212817588224) (stage 2048 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) (stage 2417851639229258349414400 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6024 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 10 4 (box 0 9671701704822212817588224) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (by decide +kernel) (by decide +kernel) (node0_6022 V) (node0_6023 V)

theorem safe0_12_10 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6024 V)

theorem node0_6025 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 11 4 (box 0 9671406574931981662947328) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node0_6026 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 11 4 (box 549755813888 9671406574932531418761216) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 549755813888 9671406574932531418761216) (stage 549755813888 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) (stage 2417851639229808105226240 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6027 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 11 4 (box 0 9671406574932531418761216) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) = true) (by decide +kernel) (by decide +kernel) (node0_6025 V) (node0_6026 V)

theorem node0_6028 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 11 4 (box 2048 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574932531418763264) (stage 2048 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) (stage 2417851639229258349414400 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6029 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 11 4 (box 0 9671406574932531418763264) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (by decide +kernel) (by decide +kernel) (node0_6027 V) (node0_6028 V)

theorem safe0_12_11 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6029 V)

theorem node0_6030 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 12 4 (box 0 9671701704822762506291200) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822762506291200) (stage 0 9671701704822762506291200 0 9671701704822762506291200) (stage 0 9671701704822762506291200 0 9671701704822762506291200) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node0_6031 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 12 4 (box 549755813888 9671701704823312262105088) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 549755813888 9671701704823312262105088) (stage 549755813888 7253850065594053912692736 2417851639229808105226240 7253850065594053912692736) (stage 2417851639229808105226240 7253850065594053912692736 2417851639229808105226240 7253850065594053912692736) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6032 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 12 4 (box 0 9671701704823312262105088) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) = true) (by decide +kernel) (by decide +kernel) (node0_6030 V) (node0_6031 V)

theorem node0_6033 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 12 4 (box 2048 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312262107136) (stage 2048 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) (stage 2417851639229258349414400 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6034 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 12 4 (box 0 9671701704823312262107136) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (by decide +kernel) (by decide +kernel) (node0_6032 V) (node0_6033 V)

theorem safe0_12_12 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6034 V)

theorem node0_6035 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 13 4 (box 0 9671406574932531452313600) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node0_6036 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 13 4 (box 33554432 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406574932531485868032) (stage 33554432 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) (stage 2417851639229258382966784 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node0_6037 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 13 4 (box 0 9671406574932531485868032) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (by decide +kernel) (by decide +kernel) (node0_6035 V) (node0_6036 V)

theorem safe0_12_13 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6037 V)

theorem node0_6038 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 14 4 (box 0 9671406574932531485870080) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node0_6039 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 14 4 (box 2048 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574932531485872128) (stage 2048 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) (stage 2417851639229258349414400 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6040 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 14 4 (box 0 9671406574932531485872128) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (by decide +kernel) (by decide +kernel) (node0_6038 V) (node0_6039 V)

theorem safe0_12_14 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6040 V)

theorem node0_6041 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 15 4 (box 0 9671701704823312329213952) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node0_6042 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 15 4 (box 2048 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312329216000) (stage 2048 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) (stage 2417851639229258349414400 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6043 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 15 4 (box 0 9671701704823312329216000) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (by decide +kernel) (by decide +kernel) (node0_6041 V) (node0_6042 V)

theorem safe0_12_15 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6043 V)

theorem node0_6044 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 16 4 (box 0 9671701722836611327068160) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node0_6045 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 16 4 (box 2048 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722836611327070208) (stage 2048 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) (stage 2417851639229258349414400 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6046 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 16 4 (box 0 9671701722836611327070208) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (by decide +kernel) (by decide +kernel) (node0_6044 V) (node0_6045 V)

theorem safe0_12_16 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6046 V)

theorem node0_6047 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 17 4 (box 0 9671701722837710838695936) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node0_6048 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 17 4 (box 2048 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node0_6049 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : NodeSafe .narrow (floorId .narrow 12) 17 4 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node0_6047 V) (node0_6048 V)

theorem safe0_12_17 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) : RowExcluded .narrow (floorId .narrow 12) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node0_6049 V)

theorem floor0_12 (V : Fast.Valid .narrow (Fast.packetCache .narrow)) (i : Fin 18) : RowExcluded .narrow (floorId .narrow 12) i := by
  fin_cases i
  · exact safe0_12_0 V
  · exact safe0_12_1 V
  · exact safe0_12_2 V
  · exact safe0_12_3 V
  · exact safe0_12_4 V
  · exact safe0_12_5 V
  · exact safe0_12_6 V
  · exact safe0_12_7 V
  · exact safe0_12_8 V
  · exact safe0_12_9 V
  · exact safe0_12_10 V
  · exact safe0_12_11 V
  · exact safe0_12_12 V
  · exact safe0_12_13 V
  · exact safe0_12_14 V
  · exact safe0_12_15 V
  · exact safe0_12_16 V
  · exact safe0_12_17 V


end GaussianChains.Band.Material
