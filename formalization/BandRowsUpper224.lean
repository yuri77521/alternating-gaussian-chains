import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node2_38762 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 0 0 (box 4835703278458516698824704 9671406556917033397651456) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38763 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 0 0 (box 4835703278458516698826752 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698826752 9671406556917033397653504) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38764 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 0 0 (box 0 9671406556917033397653504) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (by decide +kernel) (by decide +kernel) (node2_38762 V) (node2_38763 V)

theorem safe2_36_0 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38764 V)

theorem node2_38765 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 1 0 (box 4835703278458516698824704 9671406556917033431203840) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38766 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 1 0 (box 4835703278458516732379136 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516732379136 9671406556917033464758272) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38767 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 1 0 (box 0 9671406556917033464758272) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (by decide +kernel) (by decide +kernel) (node2_38765 V) (node2_38766 V)

theorem safe2_36_1 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38767 V)

theorem node2_38768 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 2 0 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe2_36_2 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38768 V)

theorem node2_38769 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 3 0 (box 0 9671406556918132909279232) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38770 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 3 0 (box 2048 9671406556918132909281280) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406556918132909281280) (stage 2048 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) (stage 2417851639229258349414400 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38771 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 3 0 (box 0 9671406556918132909281280) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (by decide +kernel) (by decide +kernel) (node2_38769 V) (node2_38770 V)

theorem safe2_36_3 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38771 V)

theorem node2_38772 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 4 0 (box 2417851639229258349412352 9671406565924232652392448) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38773 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 4 0 (box 2417851648236457604153344 9671406574931431907133440) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431907133440) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38774 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 4 0 (box 0 9671406574931431907133440) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) = true) (by decide +kernel) (by decide +kernel) (node2_38772 V) (node2_38773 V)

theorem node2_38775 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 4 0 (box 2048 9671406574931431907135488) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431907135488) (stage 2048 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) (stage 2417851639229258349414400 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38776 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 4 0 (box 0 9671406574931431907135488) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (by decide +kernel) (by decide +kernel) (node2_38774 V) (node2_38775 V)

theorem safe2_36_4 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38776 V)

theorem node2_38777 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 5 0 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem safe2_36_5 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38777 V)

theorem node2_38778 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 6 0 (box 0 9671406556918132942831616) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node2_38779 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 6 0 (box 33554432 9671406556918132976386048) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406556918132976386048) (stage 33554432 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) (stage 2417851639229258382966784 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38780 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 6 0 (box 0 9671406556918132976386048) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (by decide +kernel) (by decide +kernel) (node2_38778 V) (node2_38779 V)

theorem safe2_36_6 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38780 V)

theorem node2_38781 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 7 0 (box 2417851639229258349412352 9671406565924232685944832) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38782 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 7 0 (box 2417851648236457604153344 9671406574931431940685824) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431940685824) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38783 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 7 0 (box 0 9671406574931431940685824) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) = true) (by decide +kernel) (by decide +kernel) (node2_38781 V) (node2_38782 V)

theorem node2_38784 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 7 0 (box 33554432 9671406574931431974240256) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406574931431974240256) (stage 33554432 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) (stage 2417851639229258382966784 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38785 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 7 0 (box 0 9671406574931431974240256) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (by decide +kernel) (by decide +kernel) (node2_38783 V) (node2_38784 V)

theorem safe2_36_7 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38785 V)

theorem node2_38786 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 8 0 (box 0 9671406556918132976388096) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38787 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 8 0 (box 2048 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406556918132976390144) (stage 2048 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) (stage 2417851639229258349414400 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38788 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 8 0 (box 0 9671406556918132976390144) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (by decide +kernel) (by decide +kernel) (node2_38786 V) (node2_38787 V)

theorem safe2_36_8 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38788 V)

theorem node2_38789 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 9 0 (box 0 9671406574931431974242304) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38790 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 9 0 (box 2048 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431974244352) (stage 2048 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) (stage 2417851639229258349414400 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38791 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 9 0 (box 0 9671406574931431974244352) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (by decide +kernel) (by decide +kernel) (node2_38789 V) (node2_38790 V)

theorem safe2_36_9 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38791 V)

theorem node2_38792 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 10 0 (box 0 9671701704822212817586176) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38793 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 10 0 (box 2048 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704822212817588224) (stage 2048 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) (stage 2417851639229258349414400 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38794 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 10 0 (box 0 9671701704822212817588224) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (by decide +kernel) (by decide +kernel) (node2_38792 V) (node2_38793 V)

theorem safe2_36_10 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38794 V)

theorem node2_38795 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 11 0 (box 0 9671406574931981662947328) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38796 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 11 0 (box 549755813888 9671406574932531418761216) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 549755813888 9671406574932531418761216) (stage 549755813888 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) (stage 2417851639229808105226240 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38797 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 11 0 (box 0 9671406574932531418761216) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) = true) (by decide +kernel) (by decide +kernel) (node2_38795 V) (node2_38796 V)

theorem node2_38798 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 11 0 (box 2048 9671406574932531418763264) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574932531418763264) (stage 2048 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) (stage 2417851639229258349414400 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38799 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 11 0 (box 0 9671406574932531418763264) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (by decide +kernel) (by decide +kernel) (node2_38797 V) (node2_38798 V)

theorem safe2_36_11 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38799 V)

theorem node2_38800 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 12 0 (box 0 9671701704823312262105088) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem node2_38801 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 12 0 (box 2048 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312262107136) (stage 2048 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) (stage 2417851639229258349414400 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38802 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 12 0 (box 0 9671701704823312262107136) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (by decide +kernel) (by decide +kernel) (node2_38800 V) (node2_38801 V)

theorem safe2_36_12 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38802 V)

theorem node2_38803 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 13 0 (box 0 9671406574932531452313600) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node2_38804 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 13 0 (box 33554432 9671406574932531485868032) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 33554432 9671406574932531485868032) (stage 33554432 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) (stage 2417851639229258382966784 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38805 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 13 0 (box 0 9671406574932531485868032) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (by decide +kernel) (by decide +kernel) (node2_38803 V) (node2_38804 V)

theorem safe2_36_13 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38805 V)

theorem node2_38806 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 14 0 (box 0 9671406574932531485870080) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38807 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 14 0 (box 2048 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574932531485872128) (stage 2048 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) (stage 2417851639229258349414400 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38808 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 14 0 (box 0 9671406574932531485872128) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (by decide +kernel) (by decide +kernel) (node2_38806 V) (node2_38807 V)

theorem safe2_36_14 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38808 V)

theorem node2_38809 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 15 0 (box 0 9671701704823312329213952) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38810 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 15 0 (box 2048 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312329216000) (stage 2048 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) (stage 2417851639229258349414400 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38811 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 15 0 (box 0 9671701704823312329216000) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (by decide +kernel) (by decide +kernel) (node2_38809 V) (node2_38810 V)

theorem safe2_36_15 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38811 V)

theorem node2_38812 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 16 0 (box 0 9671701722836611327068160) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38813 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 16 0 (box 2048 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722836611327070208) (stage 2048 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) (stage 2417851639229258349414400 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38814 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 16 0 (box 0 9671701722836611327070208) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (by decide +kernel) (by decide +kernel) (node2_38812 V) (node2_38813 V)

theorem safe2_36_16 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38814 V)

theorem node2_38815 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 17 0 (box 0 9671701722837710838695936) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38816 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 17 0 (box 2048 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38817 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 36) 17 0 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node2_38815 V) (node2_38816 V)

theorem safe2_36_17 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 36) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38817 V)

theorem floor2_36 (V : Fast.Valid .upper (Fast.packetCache .upper)) (i : Fin 18) : RowExcluded .upper (floorId .upper 36) i := by
  fin_cases i
  · exact safe2_36_0 V
  · exact safe2_36_1 V
  · exact safe2_36_2 V
  · exact safe2_36_3 V
  · exact safe2_36_4 V
  · exact safe2_36_5 V
  · exact safe2_36_6 V
  · exact safe2_36_7 V
  · exact safe2_36_8 V
  · exact safe2_36_9 V
  · exact safe2_36_10 V
  · exact safe2_36_11 V
  · exact safe2_36_12 V
  · exact safe2_36_13 V
  · exact safe2_36_14 V
  · exact safe2_36_15 V
  · exact safe2_36_16 V
  · exact safe2_36_17 V


end GaussianChains.Band.Material
