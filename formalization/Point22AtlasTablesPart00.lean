import Point22AtlasTablesChecks

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt0 : Checked traceOK 0 4 :=
  Checked.of_segment (lo := 0) (count := 4) (by decide +kernel)

private theorem bandsAt4 : Checked traceOK 4 8 :=
  Checked.of_segment (lo := 4) (count := 4) (by decide +kernel)

private theorem bandsAt8 : Checked traceOK 8 12 :=
  Checked.of_segment (lo := 8) (count := 4) (by decide +kernel)

private theorem bandsAt12 : Checked traceOK 12 16 :=
  Checked.of_segment (lo := 12) (count := 4) (by decide +kernel)

private theorem bandsAt16 : Checked traceOK 16 20 :=
  Checked.of_segment (lo := 16) (count := 4) (by decide +kernel)

private theorem bandsAt20 : Checked traceOK 20 24 :=
  Checked.of_segment (lo := 20) (count := 4) (by decide +kernel)

private theorem bandsAt24 : Checked traceOK 24 28 :=
  Checked.of_segment (lo := 24) (count := 4) (by decide +kernel)

private theorem bandsAt28 : Checked traceOK 28 32 :=
  Checked.of_segment (lo := 28) (count := 4) (by decide +kernel)

private theorem bandsAt32 : Checked traceOK 32 36 :=
  Checked.of_segment (lo := 32) (count := 4) (by decide +kernel)

private theorem bandsAt36 : Checked traceOK 36 40 :=
  Checked.of_segment (lo := 36) (count := 4) (by decide +kernel)

private theorem bandsAt40 : Checked traceOK 40 44 :=
  Checked.of_segment (lo := 40) (count := 4) (by decide +kernel)

private theorem bandsAt44 : Checked traceOK 44 48 :=
  Checked.of_segment (lo := 44) (count := 4) (by decide +kernel)

private theorem bandsAt48 : Checked traceOK 48 52 :=
  Checked.of_segment (lo := 48) (count := 4) (by decide +kernel)

private theorem bandsAt52 : Checked traceOK 52 56 :=
  Checked.of_segment (lo := 52) (count := 4) (by decide +kernel)

private theorem bandsAt56 : Checked traceOK 56 60 :=
  Checked.of_segment (lo := 56) (count := 4) (by decide +kernel)

private theorem bandsAt60 : Checked traceOK 60 62 :=
  Checked.of_segment (lo := 60) (count := 2) (by decide +kernel)

theorem bandsFrom0 : Checked traceOK 0 62 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt0 bandsAt4) (Checked.join bandsAt8 bandsAt12)) (Checked.join (Checked.join bandsAt16 bandsAt20) (Checked.join bandsAt24 bandsAt28))) (Checked.join (Checked.join (Checked.join bandsAt32 bandsAt36) (Checked.join bandsAt40 bandsAt44)) (Checked.join (Checked.join bandsAt48 bandsAt52) (Checked.join bandsAt56 bandsAt60))))

private theorem rowsAt0 : Checked rowOK 0 32 :=
  Checked.of_segment (lo := 0) (count := 32) (by decide +kernel)

private theorem rowsAt32 : Checked rowOK 32 64 :=
  Checked.of_segment (lo := 32) (count := 32) (by decide +kernel)

private theorem rowsAt64 : Checked rowOK 64 96 :=
  Checked.of_segment (lo := 64) (count := 32) (by decide +kernel)

private theorem rowsAt96 : Checked rowOK 96 128 :=
  Checked.of_segment (lo := 96) (count := 32) (by decide +kernel)

private theorem rowsAt128 : Checked rowOK 128 160 :=
  Checked.of_segment (lo := 128) (count := 32) (by decide +kernel)

private theorem rowsAt160 : Checked rowOK 160 192 :=
  Checked.of_segment (lo := 160) (count := 32) (by decide +kernel)

private theorem rowsAt192 : Checked rowOK 192 224 :=
  Checked.of_segment (lo := 192) (count := 32) (by decide +kernel)

private theorem rowsAt224 : Checked rowOK 224 256 :=
  Checked.of_segment (lo := 224) (count := 32) (by decide +kernel)

private theorem rowsAt256 : Checked rowOK 256 288 :=
  Checked.of_segment (lo := 256) (count := 32) (by decide +kernel)

private theorem rowsAt288 : Checked rowOK 288 320 :=
  Checked.of_segment (lo := 288) (count := 32) (by decide +kernel)

private theorem rowsAt320 : Checked rowOK 320 352 :=
  Checked.of_segment (lo := 320) (count := 32) (by decide +kernel)

private theorem rowsAt352 : Checked rowOK 352 384 :=
  Checked.of_segment (lo := 352) (count := 32) (by decide +kernel)

private theorem rowsAt384 : Checked rowOK 384 416 :=
  Checked.of_segment (lo := 384) (count := 32) (by decide +kernel)

private theorem rowsAt416 : Checked rowOK 416 448 :=
  Checked.of_segment (lo := 416) (count := 32) (by decide +kernel)

private theorem rowsAt448 : Checked rowOK 448 480 :=
  Checked.of_segment (lo := 448) (count := 32) (by decide +kernel)

private theorem rowsAt480 : Checked rowOK 480 512 :=
  Checked.of_segment (lo := 480) (count := 32) (by decide +kernel)

private theorem rowsAt512 : Checked rowOK 512 544 :=
  Checked.of_segment (lo := 512) (count := 32) (by decide +kernel)

private theorem rowsAt544 : Checked rowOK 544 576 :=
  Checked.of_segment (lo := 544) (count := 32) (by decide +kernel)

private theorem rowsAt576 : Checked rowOK 576 608 :=
  Checked.of_segment (lo := 576) (count := 32) (by decide +kernel)

private theorem rowsAt608 : Checked rowOK 608 640 :=
  Checked.of_segment (lo := 608) (count := 32) (by decide +kernel)

private theorem rowsAt640 : Checked rowOK 640 672 :=
  Checked.of_segment (lo := 640) (count := 32) (by decide +kernel)

private theorem rowsAt672 : Checked rowOK 672 704 :=
  Checked.of_segment (lo := 672) (count := 32) (by decide +kernel)

private theorem rowsAt704 : Checked rowOK 704 736 :=
  Checked.of_segment (lo := 704) (count := 32) (by decide +kernel)

private theorem rowsAt736 : Checked rowOK 736 768 :=
  Checked.of_segment (lo := 736) (count := 32) (by decide +kernel)

private theorem rowsAt768 : Checked rowOK 768 800 :=
  Checked.of_segment (lo := 768) (count := 32) (by decide +kernel)

private theorem rowsAt800 : Checked rowOK 800 832 :=
  Checked.of_segment (lo := 800) (count := 32) (by decide +kernel)

private theorem rowsAt832 : Checked rowOK 832 864 :=
  Checked.of_segment (lo := 832) (count := 32) (by decide +kernel)

private theorem rowsAt864 : Checked rowOK 864 896 :=
  Checked.of_segment (lo := 864) (count := 32) (by decide +kernel)

private theorem rowsAt896 : Checked rowOK 896 928 :=
  Checked.of_segment (lo := 896) (count := 32) (by decide +kernel)

private theorem rowsAt928 : Checked rowOK 928 960 :=
  Checked.of_segment (lo := 928) (count := 32) (by decide +kernel)

private theorem rowsAt960 : Checked rowOK 960 992 :=
  Checked.of_segment (lo := 960) (count := 32) (by decide +kernel)

private theorem rowsAt992 : Checked rowOK 992 1000 :=
  Checked.of_segment (lo := 992) (count := 8) (by decide +kernel)

theorem rowsFrom0 : Checked rowOK 0 1000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt0 rowsAt32) (Checked.join rowsAt64 rowsAt96)) (Checked.join (Checked.join rowsAt128 rowsAt160) (Checked.join rowsAt192 rowsAt224))) (Checked.join (Checked.join (Checked.join rowsAt256 rowsAt288) (Checked.join rowsAt320 rowsAt352)) (Checked.join (Checked.join rowsAt384 rowsAt416) (Checked.join rowsAt448 rowsAt480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt512 rowsAt544) (Checked.join rowsAt576 rowsAt608)) (Checked.join (Checked.join rowsAt640 rowsAt672) (Checked.join rowsAt704 rowsAt736))) (Checked.join (Checked.join (Checked.join rowsAt768 rowsAt800) (Checked.join rowsAt832 rowsAt864)) (Checked.join (Checked.join rowsAt896 rowsAt928) (Checked.join rowsAt960 rowsAt992)))))

end GaussianChains.Point22.Atlas.Tables
