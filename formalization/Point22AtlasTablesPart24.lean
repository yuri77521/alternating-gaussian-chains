import Point22AtlasTablesPart23

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt1500 : Checked traceOK 1500 1504 :=
  Checked.of_segment (lo := 1500) (count := 4) (by decide +kernel)

private theorem bandsAt1504 : Checked traceOK 1504 1508 :=
  Checked.of_segment (lo := 1504) (count := 4) (by decide +kernel)

private theorem bandsAt1508 : Checked traceOK 1508 1512 :=
  Checked.of_segment (lo := 1508) (count := 4) (by decide +kernel)

private theorem bandsAt1512 : Checked traceOK 1512 1516 :=
  Checked.of_segment (lo := 1512) (count := 4) (by decide +kernel)

private theorem bandsAt1516 : Checked traceOK 1516 1520 :=
  Checked.of_segment (lo := 1516) (count := 4) (by decide +kernel)

private theorem bandsAt1520 : Checked traceOK 1520 1524 :=
  Checked.of_segment (lo := 1520) (count := 4) (by decide +kernel)

private theorem bandsAt1524 : Checked traceOK 1524 1528 :=
  Checked.of_segment (lo := 1524) (count := 4) (by decide +kernel)

private theorem bandsAt1528 : Checked traceOK 1528 1532 :=
  Checked.of_segment (lo := 1528) (count := 4) (by decide +kernel)

private theorem bandsAt1532 : Checked traceOK 1532 1536 :=
  Checked.of_segment (lo := 1532) (count := 4) (by decide +kernel)

private theorem bandsAt1536 : Checked traceOK 1536 1540 :=
  Checked.of_segment (lo := 1536) (count := 4) (by decide +kernel)

private theorem bandsAt1540 : Checked traceOK 1540 1544 :=
  Checked.of_segment (lo := 1540) (count := 4) (by decide +kernel)

private theorem bandsAt1544 : Checked traceOK 1544 1548 :=
  Checked.of_segment (lo := 1544) (count := 4) (by decide +kernel)

private theorem bandsAt1548 : Checked traceOK 1548 1552 :=
  Checked.of_segment (lo := 1548) (count := 4) (by decide +kernel)

private theorem bandsAt1552 : Checked traceOK 1552 1556 :=
  Checked.of_segment (lo := 1552) (count := 4) (by decide +kernel)

private theorem bandsAt1556 : Checked traceOK 1556 1560 :=
  Checked.of_segment (lo := 1556) (count := 4) (by decide +kernel)

private theorem bandsAt1560 : Checked traceOK 1560 1562 :=
  Checked.of_segment (lo := 1560) (count := 2) (by decide +kernel)

theorem bandsFrom1500 : Checked traceOK 1500 1562 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt1500 bandsAt1504) (Checked.join bandsAt1508 bandsAt1512)) (Checked.join (Checked.join bandsAt1516 bandsAt1520) (Checked.join bandsAt1524 bandsAt1528))) (Checked.join (Checked.join (Checked.join bandsAt1532 bandsAt1536) (Checked.join bandsAt1540 bandsAt1544)) (Checked.join (Checked.join bandsAt1548 bandsAt1552) (Checked.join bandsAt1556 bandsAt1560))))

private theorem rowsAt24000 : Checked rowOK 24000 24032 :=
  Checked.of_fused_segment (lo := 24000) (count := 32) (by decide +kernel)

private theorem rowsAt24032 : Checked rowOK 24032 24064 :=
  Checked.of_fused_segment (lo := 24032) (count := 32) (by decide +kernel)

private theorem rowsAt24064 : Checked rowOK 24064 24096 :=
  Checked.of_fused_segment (lo := 24064) (count := 32) (by decide +kernel)

private theorem rowsAt24096 : Checked rowOK 24096 24128 :=
  Checked.of_fused_segment (lo := 24096) (count := 32) (by decide +kernel)

private theorem rowsAt24128 : Checked rowOK 24128 24160 :=
  Checked.of_fused_segment (lo := 24128) (count := 32) (by decide +kernel)

private theorem rowsAt24160 : Checked rowOK 24160 24192 :=
  Checked.of_fused_segment (lo := 24160) (count := 32) (by decide +kernel)

private theorem rowsAt24192 : Checked rowOK 24192 24224 :=
  Checked.of_fused_segment (lo := 24192) (count := 32) (by decide +kernel)

private theorem rowsAt24224 : Checked rowOK 24224 24256 :=
  Checked.of_fused_segment (lo := 24224) (count := 32) (by decide +kernel)

private theorem rowsAt24256 : Checked rowOK 24256 24288 :=
  Checked.of_fused_segment (lo := 24256) (count := 32) (by decide +kernel)

private theorem rowsAt24288 : Checked rowOK 24288 24320 :=
  Checked.of_fused_segment (lo := 24288) (count := 32) (by decide +kernel)

private theorem rowsAt24320 : Checked rowOK 24320 24352 :=
  Checked.of_fused_segment (lo := 24320) (count := 32) (by decide +kernel)

private theorem rowsAt24352 : Checked rowOK 24352 24384 :=
  Checked.of_fused_segment (lo := 24352) (count := 32) (by decide +kernel)

private theorem rowsAt24384 : Checked rowOK 24384 24416 :=
  Checked.of_fused_segment (lo := 24384) (count := 32) (by decide +kernel)

private theorem rowsAt24416 : Checked rowOK 24416 24448 :=
  Checked.of_fused_segment (lo := 24416) (count := 32) (by decide +kernel)

private theorem rowsAt24448 : Checked rowOK 24448 24480 :=
  Checked.of_fused_segment (lo := 24448) (count := 32) (by decide +kernel)

private theorem rowsAt24480 : Checked rowOK 24480 24512 :=
  Checked.of_fused_segment (lo := 24480) (count := 32) (by decide +kernel)

private theorem rowsAt24512 : Checked rowOK 24512 24544 :=
  Checked.of_fused_segment (lo := 24512) (count := 32) (by decide +kernel)

private theorem rowsAt24544 : Checked rowOK 24544 24576 :=
  Checked.of_fused_segment (lo := 24544) (count := 32) (by decide +kernel)

private theorem rowsAt24576 : Checked rowOK 24576 24608 :=
  Checked.of_fused_segment (lo := 24576) (count := 32) (by decide +kernel)

private theorem rowsAt24608 : Checked rowOK 24608 24640 :=
  Checked.of_fused_segment (lo := 24608) (count := 32) (by decide +kernel)

private theorem rowsAt24640 : Checked rowOK 24640 24672 :=
  Checked.of_fused_segment (lo := 24640) (count := 32) (by decide +kernel)

private theorem rowsAt24672 : Checked rowOK 24672 24704 :=
  Checked.of_fused_segment (lo := 24672) (count := 32) (by decide +kernel)

private theorem rowsAt24704 : Checked rowOK 24704 24736 :=
  Checked.of_fused_segment (lo := 24704) (count := 32) (by decide +kernel)

private theorem rowsAt24736 : Checked rowOK 24736 24768 :=
  Checked.of_fused_segment (lo := 24736) (count := 32) (by decide +kernel)

private theorem rowsAt24768 : Checked rowOK 24768 24800 :=
  Checked.of_fused_segment (lo := 24768) (count := 32) (by decide +kernel)

private theorem rowsAt24800 : Checked rowOK 24800 24832 :=
  Checked.of_fused_segment (lo := 24800) (count := 32) (by decide +kernel)

private theorem rowsAt24832 : Checked rowOK 24832 24864 :=
  Checked.of_fused_segment (lo := 24832) (count := 32) (by decide +kernel)

private theorem rowsAt24864 : Checked rowOK 24864 24896 :=
  Checked.of_fused_segment (lo := 24864) (count := 32) (by decide +kernel)

private theorem rowsAt24896 : Checked rowOK 24896 24928 :=
  Checked.of_fused_segment (lo := 24896) (count := 32) (by decide +kernel)

private theorem rowsAt24928 : Checked rowOK 24928 24960 :=
  Checked.of_fused_segment (lo := 24928) (count := 32) (by decide +kernel)

private theorem rowsAt24960 : Checked rowOK 24960 24992 :=
  Checked.of_fused_segment (lo := 24960) (count := 32) (by decide +kernel)

private theorem rowsAt24992 : Checked rowOK 24992 25000 :=
  Checked.of_fused_segment (lo := 24992) (count := 8) (by decide +kernel)

theorem rowsFrom24000 : Checked rowOK 24000 25000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt24000 rowsAt24032) (Checked.join rowsAt24064 rowsAt24096)) (Checked.join (Checked.join rowsAt24128 rowsAt24160) (Checked.join rowsAt24192 rowsAt24224))) (Checked.join (Checked.join (Checked.join rowsAt24256 rowsAt24288) (Checked.join rowsAt24320 rowsAt24352)) (Checked.join (Checked.join rowsAt24384 rowsAt24416) (Checked.join rowsAt24448 rowsAt24480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt24512 rowsAt24544) (Checked.join rowsAt24576 rowsAt24608)) (Checked.join (Checked.join rowsAt24640 rowsAt24672) (Checked.join rowsAt24704 rowsAt24736))) (Checked.join (Checked.join (Checked.join rowsAt24768 rowsAt24800) (Checked.join rowsAt24832 rowsAt24864)) (Checked.join (Checked.join rowsAt24896 rowsAt24928) (Checked.join rowsAt24960 rowsAt24992)))))

end GaussianChains.Point22.Atlas.Tables
