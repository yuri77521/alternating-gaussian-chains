import Point22AtlasTablesPart11

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt750 : Checked traceOK 750 754 :=
  Checked.of_segment (lo := 750) (count := 4) (by decide +kernel)

private theorem bandsAt754 : Checked traceOK 754 758 :=
  Checked.of_segment (lo := 754) (count := 4) (by decide +kernel)

private theorem bandsAt758 : Checked traceOK 758 762 :=
  Checked.of_segment (lo := 758) (count := 4) (by decide +kernel)

private theorem bandsAt762 : Checked traceOK 762 766 :=
  Checked.of_segment (lo := 762) (count := 4) (by decide +kernel)

private theorem bandsAt766 : Checked traceOK 766 770 :=
  Checked.of_segment (lo := 766) (count := 4) (by decide +kernel)

private theorem bandsAt770 : Checked traceOK 770 774 :=
  Checked.of_segment (lo := 770) (count := 4) (by decide +kernel)

private theorem bandsAt774 : Checked traceOK 774 778 :=
  Checked.of_segment (lo := 774) (count := 4) (by decide +kernel)

private theorem bandsAt778 : Checked traceOK 778 782 :=
  Checked.of_segment (lo := 778) (count := 4) (by decide +kernel)

private theorem bandsAt782 : Checked traceOK 782 786 :=
  Checked.of_segment (lo := 782) (count := 4) (by decide +kernel)

private theorem bandsAt786 : Checked traceOK 786 790 :=
  Checked.of_segment (lo := 786) (count := 4) (by decide +kernel)

private theorem bandsAt790 : Checked traceOK 790 794 :=
  Checked.of_segment (lo := 790) (count := 4) (by decide +kernel)

private theorem bandsAt794 : Checked traceOK 794 798 :=
  Checked.of_segment (lo := 794) (count := 4) (by decide +kernel)

private theorem bandsAt798 : Checked traceOK 798 802 :=
  Checked.of_segment (lo := 798) (count := 4) (by decide +kernel)

private theorem bandsAt802 : Checked traceOK 802 806 :=
  Checked.of_segment (lo := 802) (count := 4) (by decide +kernel)

private theorem bandsAt806 : Checked traceOK 806 810 :=
  Checked.of_segment (lo := 806) (count := 4) (by decide +kernel)

private theorem bandsAt810 : Checked traceOK 810 812 :=
  Checked.of_segment (lo := 810) (count := 2) (by decide +kernel)

theorem bandsFrom750 : Checked traceOK 750 812 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt750 bandsAt754) (Checked.join bandsAt758 bandsAt762)) (Checked.join (Checked.join bandsAt766 bandsAt770) (Checked.join bandsAt774 bandsAt778))) (Checked.join (Checked.join (Checked.join bandsAt782 bandsAt786) (Checked.join bandsAt790 bandsAt794)) (Checked.join (Checked.join bandsAt798 bandsAt802) (Checked.join bandsAt806 bandsAt810))))

private theorem rowsAt12000 : Checked rowOK 12000 12032 :=
  Checked.of_fused_segment (lo := 12000) (count := 32) (by decide +kernel)

private theorem rowsAt12032 : Checked rowOK 12032 12064 :=
  Checked.of_fused_segment (lo := 12032) (count := 32) (by decide +kernel)

private theorem rowsAt12064 : Checked rowOK 12064 12096 :=
  Checked.of_fused_segment (lo := 12064) (count := 32) (by decide +kernel)

private theorem rowsAt12096 : Checked rowOK 12096 12128 :=
  Checked.of_fused_segment (lo := 12096) (count := 32) (by decide +kernel)

private theorem rowsAt12128 : Checked rowOK 12128 12160 :=
  Checked.of_fused_segment (lo := 12128) (count := 32) (by decide +kernel)

private theorem rowsAt12160 : Checked rowOK 12160 12192 :=
  Checked.of_fused_segment (lo := 12160) (count := 32) (by decide +kernel)

private theorem rowsAt12192 : Checked rowOK 12192 12224 :=
  Checked.of_fused_segment (lo := 12192) (count := 32) (by decide +kernel)

private theorem rowsAt12224 : Checked rowOK 12224 12256 :=
  Checked.of_fused_segment (lo := 12224) (count := 32) (by decide +kernel)

private theorem rowsAt12256 : Checked rowOK 12256 12288 :=
  Checked.of_fused_segment (lo := 12256) (count := 32) (by decide +kernel)

private theorem rowsAt12288 : Checked rowOK 12288 12320 :=
  Checked.of_fused_segment (lo := 12288) (count := 32) (by decide +kernel)

private theorem rowsAt12320 : Checked rowOK 12320 12352 :=
  Checked.of_fused_segment (lo := 12320) (count := 32) (by decide +kernel)

private theorem rowsAt12352 : Checked rowOK 12352 12384 :=
  Checked.of_fused_segment (lo := 12352) (count := 32) (by decide +kernel)

private theorem rowsAt12384 : Checked rowOK 12384 12416 :=
  Checked.of_fused_segment (lo := 12384) (count := 32) (by decide +kernel)

private theorem rowsAt12416 : Checked rowOK 12416 12448 :=
  Checked.of_fused_segment (lo := 12416) (count := 32) (by decide +kernel)

private theorem rowsAt12448 : Checked rowOK 12448 12480 :=
  Checked.of_fused_segment (lo := 12448) (count := 32) (by decide +kernel)

private theorem rowsAt12480 : Checked rowOK 12480 12512 :=
  Checked.of_fused_segment (lo := 12480) (count := 32) (by decide +kernel)

private theorem rowsAt12512 : Checked rowOK 12512 12544 :=
  Checked.of_fused_segment (lo := 12512) (count := 32) (by decide +kernel)

private theorem rowsAt12544 : Checked rowOK 12544 12576 :=
  Checked.of_fused_segment (lo := 12544) (count := 32) (by decide +kernel)

private theorem rowsAt12576 : Checked rowOK 12576 12608 :=
  Checked.of_fused_segment (lo := 12576) (count := 32) (by decide +kernel)

private theorem rowsAt12608 : Checked rowOK 12608 12640 :=
  Checked.of_fused_segment (lo := 12608) (count := 32) (by decide +kernel)

private theorem rowsAt12640 : Checked rowOK 12640 12672 :=
  Checked.of_fused_segment (lo := 12640) (count := 32) (by decide +kernel)

private theorem rowsAt12672 : Checked rowOK 12672 12704 :=
  Checked.of_fused_segment (lo := 12672) (count := 32) (by decide +kernel)

private theorem rowsAt12704 : Checked rowOK 12704 12736 :=
  Checked.of_fused_segment (lo := 12704) (count := 32) (by decide +kernel)

private theorem rowsAt12736 : Checked rowOK 12736 12768 :=
  Checked.of_fused_segment (lo := 12736) (count := 32) (by decide +kernel)

private theorem rowsAt12768 : Checked rowOK 12768 12800 :=
  Checked.of_fused_segment (lo := 12768) (count := 32) (by decide +kernel)

private theorem rowsAt12800 : Checked rowOK 12800 12832 :=
  Checked.of_fused_segment (lo := 12800) (count := 32) (by decide +kernel)

private theorem rowsAt12832 : Checked rowOK 12832 12864 :=
  Checked.of_fused_segment (lo := 12832) (count := 32) (by decide +kernel)

private theorem rowsAt12864 : Checked rowOK 12864 12896 :=
  Checked.of_fused_segment (lo := 12864) (count := 32) (by decide +kernel)

private theorem rowsAt12896 : Checked rowOK 12896 12928 :=
  Checked.of_fused_segment (lo := 12896) (count := 32) (by decide +kernel)

private theorem rowsAt12928 : Checked rowOK 12928 12960 :=
  Checked.of_fused_segment (lo := 12928) (count := 32) (by decide +kernel)

private theorem rowsAt12960 : Checked rowOK 12960 12992 :=
  Checked.of_fused_segment (lo := 12960) (count := 32) (by decide +kernel)

private theorem rowsAt12992 : Checked rowOK 12992 13000 :=
  Checked.of_fused_segment (lo := 12992) (count := 8) (by decide +kernel)

theorem rowsFrom12000 : Checked rowOK 12000 13000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt12000 rowsAt12032) (Checked.join rowsAt12064 rowsAt12096)) (Checked.join (Checked.join rowsAt12128 rowsAt12160) (Checked.join rowsAt12192 rowsAt12224))) (Checked.join (Checked.join (Checked.join rowsAt12256 rowsAt12288) (Checked.join rowsAt12320 rowsAt12352)) (Checked.join (Checked.join rowsAt12384 rowsAt12416) (Checked.join rowsAt12448 rowsAt12480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt12512 rowsAt12544) (Checked.join rowsAt12576 rowsAt12608)) (Checked.join (Checked.join rowsAt12640 rowsAt12672) (Checked.join rowsAt12704 rowsAt12736))) (Checked.join (Checked.join (Checked.join rowsAt12768 rowsAt12800) (Checked.join rowsAt12832 rowsAt12864)) (Checked.join (Checked.join rowsAt12896 rowsAt12928) (Checked.join rowsAt12960 rowsAt12992)))))

end GaussianChains.Point22.Atlas.Tables
