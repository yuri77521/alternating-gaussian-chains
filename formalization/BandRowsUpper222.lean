import BandLocalProof
import BandNodeData

namespace GaussianChains.Band.Material
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem node2_38634 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 0 0 (box 4835703278458516698824704 9671406556917033397651456) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) (stage 7253554917687775048237056 9671406556917033397651456 7253554917687775048237056 9671406556917033397651456) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38635 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 0 0 (box 4835703278458516698826752 9671406556917033397653504) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698826752 9671406556917033397653504) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) (stage 4835703278458516698826752 7253554917687775048241152 4835703278458516698826752 7253554917687775048241152) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38636 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 0 0 (box 0 9671406556917033397653504) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) (stage 4835703278458516698824704 9671406556917033397653504 4835703278458516698824704 9671406556917033397653504) = true) (by decide +kernel) (by decide +kernel) (node2_38634 V) (node2_38635 V)

theorem safe2_34_0 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 0 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38636 V)

theorem node2_38637 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 1 0 (box 4835703278458516698824704 9671406556917033431203840) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516698824704 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) (stage 7253554917687775048237056 9671406556917033431203840 7253554917687775048237056 9671406556917033431203840) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38638 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 1 0 (box 4835703278458516732379136 9671406556917033464758272) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 4835703278458516732379136 9671406556917033464758272) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) (stage 4835703278458516732379136 7253554917687775115345920 4835703278458516732379136 7253554917687775115345920) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38639 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 1 0 (box 0 9671406556917033464758272) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) (stage 4835703278458516698824704 9671406556917033464758272 4835703278458516698824704 9671406556917033464758272) = true) (by decide +kernel) (by decide +kernel) (node2_38637 V) (node2_38638 V)

theorem safe2_34_1 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 1 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38639 V)

theorem node2_38640 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 2 0 (box 0 9671406556917033464762368) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) (stage 0 9671406556917033464762368 0 9671406556917033464762368) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem safe2_34_2 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 2 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38640 V)

theorem node2_38641 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 3 0 (box 0 9671406556918132909279232) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) (stage 2417851639229258349412352 9671406556918132909279232 2417851639229258349412352 9671406556918132909279232) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38642 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 3 0 (box 2417851639229258349414400 7253554917688324804055040) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349414400 7253554917688324804055040) (stage 2417851639229258349414400 7253554917688324804055040 2417851639229258349414400 7253554917688324804055040) (stage 2417851639229258349414400 7253554917688324804055040 2417851639229258349414400 7253554917688324804055040) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38643 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 3 0 (box 2417851639229808105228288 7253554917688874559868928) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229808105228288 7253554917688874559868928) (stage 2417851639229808105228288 4835703278459616210456576 2417851639229808105228288 4835703278459616210456576) (stage 2417851639229808105228288 4835703278459616210456576 2417851639229808105228288 4835703278459616210456576) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38644 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 3 0 (box 2048 9671406556918132909281280) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 2048 9671406556918132909281280) (stage 2048 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) (stage 2417851639229258349414400 7253554917688874559868928 2417851639229258349414400 7253554917688874559868928) = true) (by decide +kernel) (by decide +kernel) (node2_38642 V) (node2_38643 V)

theorem node2_38645 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 3 0 (box 0 9671406556918132909281280) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) (stage 0 9671406556918132909281280 0 9671406556918132909281280) = true) (by decide +kernel) (by decide +kernel) (node2_38641 V) (node2_38644 V)

theorem safe2_34_3 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 3 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38645 V)

theorem node2_38646 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 4 0 (box 2417851639229258349412352 9671406565924232652392448) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) (stage 4835703278458516698824704 9671406565924232652392448 4835703278458516698824704 9671406565924232652392448) = true) (.transfer (.curvature 3 5)) (by decide +kernel)

theorem node2_38647 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 4 0 (box 2417851648236457604153344 9671406574931431907133440) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431907133440) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) (stage 2417851648236457604153344 7253554935702173557721088 2417851648236457604153344 7253554935702173557721088) = true) (.transfer (.curvature 3 5)) (by decide +kernel)

theorem node2_38648 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 4 0 (box 0 9671406574931431907133440) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) (stage 2417851639229258349412352 9671406574931431907133440 2417851639229258349412352 9671406574931431907133440) = true) (by decide +kernel) (by decide +kernel) (node2_38646 V) (node2_38647 V)

theorem node2_38649 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 4 0 (box 2417851639229258349414400 7253554926694974302982144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349414400 7253554926694974302982144) (stage 2417851639229258349414400 7253554926694974302982144 2417851639229258349414400 7253554926694974302982144) (stage 2417851639229258349414400 7253554926694974302982144 2417851639229258349414400 7253554926694974302982144) = true) (.transfer (.curvature 3 5)) (by decide +kernel)

theorem node2_38650 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 4 0 (box 2417851648236457604155392 7253554935702173557723136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604155392 7253554935702173557723136) (stage 2417851648236457604155392 4835703296472915208310784 2417851648236457604155392 4835703296472915208310784) (stage 2417851648236457604155392 4835703296472915208310784 2417851648236457604155392 4835703296472915208310784) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38651 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 4 0 (box 2048 9671406574931431907135488) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 2048 9671406574931431907135488) (stage 2048 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) (stage 2417851639229258349414400 7253554935702173557723136 2417851639229258349414400 7253554935702173557723136) = true) (by decide +kernel) (by decide +kernel) (node2_38649 V) (node2_38650 V)

theorem node2_38652 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 4 0 (box 0 9671406574931431907135488) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) (stage 0 9671406574931431907135488 0 9671406574931431907135488) = true) (by decide +kernel) (by decide +kernel) (node2_38648 V) (node2_38651 V)

theorem safe2_34_4 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 4 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38652 V)

theorem node2_38653 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 5 0 (box 0 9671701704822212750479360) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) (stage 0 9671701704822212750479360 0 9671701704822212750479360) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem safe2_34_5 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 5 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38653 V)

theorem node2_38654 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 6 0 (box 0 9671406556918132942831616) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) (stage 2417851639229258349412352 9671406556918132942831616 2417851639229258349412352 9671406556918132942831616) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node2_38655 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 6 0 (box 2417851639229258382966784 7253554917688324871159808) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258382966784 7253554917688324871159808) (stage 2417851639229258382966784 7253554917688324871159808 2417851639229258382966784 7253554917688324871159808) (stage 2417851639229258382966784 7253554917688324871159808 2417851639229258382966784 7253554917688324871159808) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node2_38656 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 6 0 (box 2417851639229808138780672 7253554917688874626973696) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229808138780672 7253554917688874626973696) (stage 2417851639229808138780672 4835703278459616277561344 2417851639229808138780672 4835703278459616277561344) (stage 2417851639229808138780672 4835703278459616277561344 2417851639229808138780672 4835703278459616277561344) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38657 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 6 0 (box 33554432 9671406556918132976386048) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 33554432 9671406556918132976386048) (stage 33554432 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) (stage 2417851639229258382966784 7253554917688874626973696 2417851639229258382966784 7253554917688874626973696) = true) (by decide +kernel) (by decide +kernel) (node2_38655 V) (node2_38656 V)

theorem node2_38658 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 6 0 (box 0 9671406556918132976386048) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) (stage 0 9671406556918132976386048 0 9671406556918132976386048) = true) (by decide +kernel) (by decide +kernel) (node2_38654 V) (node2_38657 V)

theorem safe2_34_6 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 6 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38658 V)

theorem node2_38659 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 7 0 (box 2417851639229258349412352 9671406565924232685944832) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349412352 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) (stage 4835703278458516698824704 9671406565924232685944832 4835703278458516698824704 9671406565924232685944832) = true) (.transfer (.curvature 1 3)) (by decide +kernel)

theorem node2_38660 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 7 0 (box 2417851648236457604153344 9671406574931431940685824) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457604153344 9671406574931431940685824) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) (stage 2417851648236457604153344 7253554935702173591273472 2417851648236457604153344 7253554935702173591273472) = true) (.transfer (.curvature 1 3)) (by decide +kernel)

theorem node2_38661 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 7 0 (box 0 9671406574931431940685824) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 0 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) (stage 2417851639229258349412352 9671406574931431940685824 2417851639229258349412352 9671406574931431940685824) = true) (by decide +kernel) (by decide +kernel) (node2_38659 V) (node2_38660 V)

theorem node2_38662 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 7 0 (box 2417851639229258382966784 7253554926694974370086912) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258382966784 7253554926694974370086912) (stage 2417851639229258382966784 7253554926694974370086912 2417851639229258382966784 7253554926694974370086912) (stage 2417851639229258382966784 7253554926694974370086912 2417851639229258382966784 7253554926694974370086912) = true) (.transfer (.curvature 1 3)) (by decide +kernel)

theorem node2_38663 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 7 0 (box 2417851648236457637707776 7253554935702173624827904) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851648236457637707776 7253554935702173624827904) (stage 2417851648236457637707776 4835703296472915275415552 2417851648236457637707776 4835703296472915275415552) (stage 2417851648236457637707776 4835703296472915275415552 2417851648236457637707776 4835703296472915275415552) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38664 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 7 0 (box 33554432 9671406574931431974240256) :=
  nodeSafe_split 3 2048 (by decide +kernel : checkChamber (box 33554432 9671406574931431974240256) (stage 33554432 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) (stage 2417851639229258382966784 7253554935702173624827904 2417851639229258382966784 7253554935702173624827904) = true) (by decide +kernel) (by decide +kernel) (node2_38662 V) (node2_38663 V)

theorem node2_38665 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 7 0 (box 0 9671406574931431974240256) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) (stage 0 9671406574931431974240256 0 9671406574931431974240256) = true) (by decide +kernel) (by decide +kernel) (node2_38661 V) (node2_38664 V)

theorem safe2_34_7 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 7 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38665 V)

theorem node2_38666 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 8 0 (box 0 9671406556918132976388096) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) (stage 0 9671406556918132976388096 0 9671406556918132976388096) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38667 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 8 0 (box 2048 9671406556918132976390144) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406556918132976390144) (stage 2048 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) (stage 2417851639229258349414400 7253554917688874626977792 2417851639229258349414400 7253554917688874626977792) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38668 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 8 0 (box 0 9671406556918132976390144) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) (stage 0 9671406556918132976390144 0 9671406556918132976390144) = true) (by decide +kernel) (by decide +kernel) (node2_38666 V) (node2_38667 V)

theorem safe2_34_8 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 8 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38668 V)

theorem node2_38669 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 9 0 (box 0 9671406574931431974242304) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) (stage 0 9671406574931431974242304 0 9671406574931431974242304) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38670 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 9 0 (box 2048 9671406574931431974244352) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574931431974244352) (stage 2048 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) (stage 2417851639229258349414400 7253554935702173624832000 2417851639229258349414400 7253554935702173624832000) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38671 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 9 0 (box 0 9671406574931431974244352) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) (stage 0 9671406574931431974244352 0 9671406574931431974244352) = true) (by decide +kernel) (by decide +kernel) (node2_38669 V) (node2_38670 V)

theorem safe2_34_9 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 9 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38671 V)

theorem node2_38672 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 10 0 (box 0 9671701704822212817586176) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) (stage 0 9671701704822212817586176 0 9671701704822212817586176) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38673 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 10 0 (box 2048 9671701704822212817588224) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704822212817588224) (stage 2048 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) (stage 2417851639229258349414400 7253850065592954468175872 2417851639229258349414400 7253850065592954468175872) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38674 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 10 0 (box 0 9671701704822212817588224) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) (stage 0 9671701704822212817588224 0 9671701704822212817588224) = true) (by decide +kernel) (by decide +kernel) (node2_38672 V) (node2_38673 V)

theorem safe2_34_10 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 10 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38674 V)

theorem node2_38675 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 11 0 (box 0 9671406574931981662947328) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) (stage 0 9671406574931981662947328 0 9671406574931981662947328) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38676 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 11 0 (box 549755813888 9671406574932531418761216) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 549755813888 9671406574932531418761216) (stage 549755813888 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) (stage 2417851639229808105226240 7253554935703273069348864 2417851639229808105226240 7253554935703273069348864) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38677 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 11 0 (box 0 9671406574932531418761216) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) (stage 0 9671406574932531418761216 0 9671406574932531418761216) = true) (by decide +kernel) (by decide +kernel) (node2_38675 V) (node2_38676 V)

theorem node2_38678 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 11 0 (box 2417851639229258349414400 7253554935702723313537024) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258349414400 7253554935702723313537024) (stage 2417851639229258349414400 7253554935702723313537024 2417851639229258349414400 7253554935702723313537024) (stage 2417851639229258349414400 7253554935702723313537024 2417851639229258349414400 7253554935702723313537024) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38679 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 11 0 (box 2417851639229808105228288 7253554935703273069350912) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229808105228288 7253554935703273069350912) (stage 2417851639229808105228288 4835703287466815465197568 2417851639229808105228288 4835703287466815465197568) (stage 2417851639229808105228288 4835703287466815465197568 2417851639229808105228288 4835703287466815465197568) = true) (.transfer (.curvature 0 5)) (by decide +kernel)

theorem node2_38680 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 11 0 (box 2048 9671406574932531418763264) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 2048 9671406574932531418763264) (stage 2048 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) (stage 2417851639229258349414400 7253554935703273069350912 2417851639229258349414400 7253554935703273069350912) = true) (by decide +kernel) (by decide +kernel) (node2_38678 V) (node2_38679 V)

theorem node2_38681 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 11 0 (box 0 9671406574932531418763264) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) (stage 0 9671406574932531418763264 0 9671406574932531418763264) = true) (by decide +kernel) (by decide +kernel) (node2_38677 V) (node2_38680 V)

theorem safe2_34_11 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 11 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38681 V)

theorem node2_38682 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 12 0 (box 0 9671701704822762506291200) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704822762506291200) (stage 0 9671701704822762506291200 0 9671701704822762506291200) (stage 0 9671701704822762506291200 0 9671701704822762506291200) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38683 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 12 0 (box 549755813888 9671701704823312262105088) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 549755813888 9671701704823312262105088) (stage 549755813888 7253850065594053912692736 2417851639229808105226240 7253850065594053912692736) (stage 2417851639229808105226240 7253850065594053912692736 2417851639229808105226240 7253850065594053912692736) = true) (.transfer (.curvature 0 2)) (by decide +kernel)

theorem node2_38684 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 12 0 (box 0 9671701704823312262105088) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) (stage 0 9671701704823312262105088 0 9671701704823312262105088) = true) (by decide +kernel) (by decide +kernel) (node2_38682 V) (node2_38683 V)

theorem node2_38685 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 12 0 (box 2048 9671701704823312262107136) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312262107136) (stage 2048 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) (stage 2417851639229258349414400 7253850065594053912694784 2417851639229258349414400 7253850065594053912694784) = true) (.transfer (.curvature 0 4)) (by decide +kernel)

theorem node2_38686 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 12 0 (box 0 9671701704823312262107136) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) (stage 0 9671701704823312262107136 0 9671701704823312262107136) = true) (by decide +kernel) (by decide +kernel) (node2_38684 V) (node2_38685 V)

theorem safe2_34_12 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 12 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38686 V)

theorem node2_38687 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 13 0 (box 0 9671406574932531452313600) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) (stage 0 9671406574932531452313600 0 9671406574932531452313600) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node2_38688 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 13 0 (box 2417851639229258382966784 7253554935702723380641792) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229258382966784 7253554935702723380641792) (stage 2417851639229258382966784 7253554935702723380641792 2417851639229258382966784 7253554935702723380641792) (stage 2417851639229258382966784 7253554935702723380641792 2417851639229258382966784 7253554935702723380641792) = true) (.transfer (.curvature 1 2)) (by decide +kernel)

theorem node2_38689 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 13 0 (box 2417851639229808138780672 7253554935703273136455680) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2417851639229808138780672 7253554935703273136455680) (stage 2417851639229808138780672 4835703287466815532302336 2417851639229808138780672 4835703287466815532302336) (stage 2417851639229808138780672 4835703287466815532302336 2417851639229808138780672 4835703287466815532302336) = true) (.transfer (.curvature 1 5)) (by decide +kernel)

theorem node2_38690 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 13 0 (box 33554432 9671406574932531485868032) :=
  nodeSafe_split 2 2048 (by decide +kernel : checkChamber (box 33554432 9671406574932531485868032) (stage 33554432 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) (stage 2417851639229258382966784 7253554935703273136455680 2417851639229258382966784 7253554935703273136455680) = true) (by decide +kernel) (by decide +kernel) (node2_38688 V) (node2_38689 V)

theorem node2_38691 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 13 0 (box 0 9671406574932531485868032) :=
  nodeSafe_split 1 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) (stage 0 9671406574932531485868032 0 9671406574932531485868032) = true) (by decide +kernel) (by decide +kernel) (node2_38687 V) (node2_38690 V)

theorem safe2_34_13 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 13 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38691 V)

theorem node2_38692 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 14 0 (box 0 9671406574932531485870080) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) (stage 0 9671406574932531485870080 0 9671406574932531485870080) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38693 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 14 0 (box 2048 9671406574932531485872128) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671406574932531485872128) (stage 2048 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) (stage 2417851639229258349414400 7253554935703273136459776 2417851639229258349414400 7253554935703273136459776) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38694 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 14 0 (box 0 9671406574932531485872128) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) (stage 0 9671406574932531485872128 0 9671406574932531485872128) = true) (by decide +kernel) (by decide +kernel) (node2_38692 V) (node2_38693 V)

theorem safe2_34_14 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 14 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38694 V)

theorem node2_38695 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 15 0 (box 0 9671701704823312329213952) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) (stage 0 9671701704823312329213952 0 9671701704823312329213952) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38696 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 15 0 (box 2048 9671701704823312329216000) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701704823312329216000) (stage 2048 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) (stage 2417851639229258349414400 7253850065594053979803648 2417851639229258349414400 7253850065594053979803648) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38697 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 15 0 (box 0 9671701704823312329216000) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) (stage 0 9671701704823312329216000 0 9671701704823312329216000) = true) (by decide +kernel) (by decide +kernel) (node2_38695 V) (node2_38696 V)

theorem safe2_34_15 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 15 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38697 V)

theorem node2_38698 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 16 0 (box 0 9671701722836611327068160) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) (stage 0 9671701722836611327068160 0 9671701722836611327068160) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38699 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 16 0 (box 2048 9671701722836611327070208) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722836611327070208) (stage 2048 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) (stage 2417851639229258349414400 7253850083607352977657856 2417851639229258349414400 7253850083607352977657856) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38700 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 16 0 (box 0 9671701722836611327070208) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) (stage 0 9671701722836611327070208 0 9671701722836611327070208) = true) (by decide +kernel) (by decide +kernel) (node2_38698 V) (node2_38699 V)

theorem safe2_34_16 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 16 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38700 V)

theorem node2_38701 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 17 0 (box 0 9671701722837710838695936) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) (stage 0 9671701722837710838695936 0 9671701722837710838695936) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38702 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 17 0 (box 2048 9671701722837710838697984) :=
  nodeSafe_leaf V (by decide +kernel : checkChamber (box 2048 9671701722837710838697984) (stage 2048 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) (stage 2417851639229258349414400 7253850083608452489285632 2417851639229258349414400 7253850083608452489285632) = true) (.transfer (.curvature 0 1)) (by decide +kernel)

theorem node2_38703 (V : Fast.Valid .upper (Fast.packetCache .upper)) : NodeSafe .upper (floorId .upper 34) 17 0 (box 0 9671701722837710838697984) :=
  nodeSafe_split 0 2048 (by decide +kernel : checkChamber (box 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) (stage 0 9671701722837710838697984 0 9671701722837710838697984) = true) (by decide +kernel) (by decide +kernel) (node2_38701 V) (node2_38702 V)

theorem safe2_34_17 (V : Fast.Valid .upper (Fast.packetCache .upper)) : RowExcluded .upper (floorId .upper 34) 17 :=
  rowExcluded_of_nodeSafe (by decide +kernel) (node2_38703 V)

theorem floor2_34 (V : Fast.Valid .upper (Fast.packetCache .upper)) (i : Fin 18) : RowExcluded .upper (floorId .upper 34) i := by
  fin_cases i
  · exact safe2_34_0 V
  · exact safe2_34_1 V
  · exact safe2_34_2 V
  · exact safe2_34_3 V
  · exact safe2_34_4 V
  · exact safe2_34_5 V
  · exact safe2_34_6 V
  · exact safe2_34_7 V
  · exact safe2_34_8 V
  · exact safe2_34_9 V
  · exact safe2_34_10 V
  · exact safe2_34_11 V
  · exact safe2_34_12 V
  · exact safe2_34_13 V
  · exact safe2_34_14 V
  · exact safe2_34_15 V
  · exact safe2_34_16 V
  · exact safe2_34_17 V


end GaussianChains.Band.Material
