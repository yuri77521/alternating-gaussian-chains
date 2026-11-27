import Point22AtlasTablesPart00

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt62 : Checked traceOK 62 66 :=
  Checked.of_segment (lo := 62) (count := 4) (by decide +kernel)

private theorem bandsAt66 : Checked traceOK 66 70 :=
  Checked.of_segment (lo := 66) (count := 4) (by decide +kernel)

private theorem bandsAt70 : Checked traceOK 70 74 :=
  Checked.of_segment (lo := 70) (count := 4) (by decide +kernel)

private theorem bandsAt74 : Checked traceOK 74 78 :=
  Checked.of_segment (lo := 74) (count := 4) (by decide +kernel)

private theorem bandsAt78 : Checked traceOK 78 82 :=
  Checked.of_segment (lo := 78) (count := 4) (by decide +kernel)

private theorem bandsAt82 : Checked traceOK 82 86 :=
  Checked.of_segment (lo := 82) (count := 4) (by decide +kernel)

private theorem bandsAt86 : Checked traceOK 86 90 :=
  Checked.of_segment (lo := 86) (count := 4) (by decide +kernel)

private theorem bandsAt90 : Checked traceOK 90 94 :=
  Checked.of_segment (lo := 90) (count := 4) (by decide +kernel)

private theorem bandsAt94 : Checked traceOK 94 98 :=
  Checked.of_segment (lo := 94) (count := 4) (by decide +kernel)

private theorem bandsAt98 : Checked traceOK 98 102 :=
  Checked.of_segment (lo := 98) (count := 4) (by decide +kernel)

private theorem bandsAt102 : Checked traceOK 102 106 :=
  Checked.of_segment (lo := 102) (count := 4) (by decide +kernel)

private theorem bandsAt106 : Checked traceOK 106 110 :=
  Checked.of_segment (lo := 106) (count := 4) (by decide +kernel)

private theorem bandsAt110 : Checked traceOK 110 114 :=
  Checked.of_segment (lo := 110) (count := 4) (by decide +kernel)

private theorem bandsAt114 : Checked traceOK 114 118 :=
  Checked.of_segment (lo := 114) (count := 4) (by decide +kernel)

private theorem bandsAt118 : Checked traceOK 118 122 :=
  Checked.of_segment (lo := 118) (count := 4) (by decide +kernel)

private theorem bandsAt122 : Checked traceOK 122 125 :=
  Checked.of_segment (lo := 122) (count := 3) (by decide +kernel)

theorem bandsFrom62 : Checked traceOK 62 125 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt62 bandsAt66) (Checked.join bandsAt70 bandsAt74)) (Checked.join (Checked.join bandsAt78 bandsAt82) (Checked.join bandsAt86 bandsAt90))) (Checked.join (Checked.join (Checked.join bandsAt94 bandsAt98) (Checked.join bandsAt102 bandsAt106)) (Checked.join (Checked.join bandsAt110 bandsAt114) (Checked.join bandsAt118 bandsAt122))))

private theorem rowsAt1000 : Checked rowOK 1000 1032 :=
  Checked.of_segment (lo := 1000) (count := 32) (by decide +kernel)

private theorem rowsAt1032 : Checked rowOK 1032 1064 :=
  Checked.of_segment (lo := 1032) (count := 32) (by decide +kernel)

private theorem rowsAt1064 : Checked rowOK 1064 1096 :=
  Checked.of_segment (lo := 1064) (count := 32) (by decide +kernel)

private theorem rowsAt1096 : Checked rowOK 1096 1128 :=
  Checked.of_segment (lo := 1096) (count := 32) (by decide +kernel)

private theorem rowsAt1128 : Checked rowOK 1128 1160 :=
  Checked.of_segment (lo := 1128) (count := 32) (by decide +kernel)

private theorem rowsAt1160 : Checked rowOK 1160 1192 :=
  Checked.of_segment (lo := 1160) (count := 32) (by decide +kernel)

private theorem rowsAt1192 : Checked rowOK 1192 1224 :=
  Checked.of_segment (lo := 1192) (count := 32) (by decide +kernel)

private theorem rowsAt1224 : Checked rowOK 1224 1256 :=
  Checked.of_segment (lo := 1224) (count := 32) (by decide +kernel)

private theorem rowsAt1256 : Checked rowOK 1256 1288 :=
  Checked.of_segment (lo := 1256) (count := 32) (by decide +kernel)

private theorem rowsAt1288 : Checked rowOK 1288 1320 :=
  Checked.of_segment (lo := 1288) (count := 32) (by decide +kernel)

private theorem rowsAt1320 : Checked rowOK 1320 1352 :=
  Checked.of_segment (lo := 1320) (count := 32) (by decide +kernel)

private theorem rowsAt1352 : Checked rowOK 1352 1384 :=
  Checked.of_segment (lo := 1352) (count := 32) (by decide +kernel)

private theorem rowsAt1384 : Checked rowOK 1384 1416 :=
  Checked.of_segment (lo := 1384) (count := 32) (by decide +kernel)

private theorem rowsAt1416 : Checked rowOK 1416 1448 :=
  Checked.of_segment (lo := 1416) (count := 32) (by decide +kernel)

private theorem rowsAt1448 : Checked rowOK 1448 1480 :=
  Checked.of_segment (lo := 1448) (count := 32) (by decide +kernel)

private theorem rowsAt1480 : Checked rowOK 1480 1512 :=
  Checked.of_segment (lo := 1480) (count := 32) (by decide +kernel)

private theorem rowsAt1512 : Checked rowOK 1512 1544 :=
  Checked.of_segment (lo := 1512) (count := 32) (by decide +kernel)

private theorem rowsAt1544 : Checked rowOK 1544 1576 :=
  Checked.of_segment (lo := 1544) (count := 32) (by decide +kernel)

private theorem rowsAt1576 : Checked rowOK 1576 1608 :=
  Checked.of_segment (lo := 1576) (count := 32) (by decide +kernel)

private theorem rowsAt1608 : Checked rowOK 1608 1640 :=
  Checked.of_segment (lo := 1608) (count := 32) (by decide +kernel)

private theorem rowsAt1640 : Checked rowOK 1640 1672 :=
  Checked.of_segment (lo := 1640) (count := 32) (by decide +kernel)

private theorem rowsAt1672 : Checked rowOK 1672 1704 :=
  Checked.of_segment (lo := 1672) (count := 32) (by decide +kernel)

private theorem rowsAt1704 : Checked rowOK 1704 1736 :=
  Checked.of_segment (lo := 1704) (count := 32) (by decide +kernel)

private theorem rowsAt1736 : Checked rowOK 1736 1768 :=
  Checked.of_segment (lo := 1736) (count := 32) (by decide +kernel)

private theorem rowsAt1768 : Checked rowOK 1768 1800 :=
  Checked.of_segment (lo := 1768) (count := 32) (by decide +kernel)

private theorem rowsAt1800 : Checked rowOK 1800 1832 :=
  Checked.of_segment (lo := 1800) (count := 32) (by decide +kernel)

private theorem rowsAt1832 : Checked rowOK 1832 1864 :=
  Checked.of_segment (lo := 1832) (count := 32) (by decide +kernel)

private theorem rowsAt1864 : Checked rowOK 1864 1896 :=
  Checked.of_segment (lo := 1864) (count := 32) (by decide +kernel)

private theorem rowsAt1896 : Checked rowOK 1896 1928 :=
  Checked.of_segment (lo := 1896) (count := 32) (by decide +kernel)

private theorem rowsAt1928 : Checked rowOK 1928 1960 :=
  Checked.of_segment (lo := 1928) (count := 32) (by decide +kernel)

private theorem rowsAt1960 : Checked rowOK 1960 1992 :=
  Checked.of_segment (lo := 1960) (count := 32) (by decide +kernel)

private theorem rowsAt1992 : Checked rowOK 1992 2000 :=
  Checked.of_segment (lo := 1992) (count := 8) (by decide +kernel)

theorem rowsFrom1000 : Checked rowOK 1000 2000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt1000 rowsAt1032) (Checked.join rowsAt1064 rowsAt1096)) (Checked.join (Checked.join rowsAt1128 rowsAt1160) (Checked.join rowsAt1192 rowsAt1224))) (Checked.join (Checked.join (Checked.join rowsAt1256 rowsAt1288) (Checked.join rowsAt1320 rowsAt1352)) (Checked.join (Checked.join rowsAt1384 rowsAt1416) (Checked.join rowsAt1448 rowsAt1480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt1512 rowsAt1544) (Checked.join rowsAt1576 rowsAt1608)) (Checked.join (Checked.join rowsAt1640 rowsAt1672) (Checked.join rowsAt1704 rowsAt1736))) (Checked.join (Checked.join (Checked.join rowsAt1768 rowsAt1800) (Checked.join rowsAt1832 rowsAt1864)) (Checked.join (Checked.join rowsAt1896 rowsAt1928) (Checked.join rowsAt1960 rowsAt1992)))))

end GaussianChains.Point22.Atlas.Tables
