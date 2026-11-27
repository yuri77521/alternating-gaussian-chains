import Point22AtlasTablesPart07
import Point22AtlasTablesFused

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt500 : Checked traceOK 500 504 :=
  Checked.of_segment (lo := 500) (count := 4) (by decide +kernel)

private theorem bandsAt504 : Checked traceOK 504 508 :=
  Checked.of_segment (lo := 504) (count := 4) (by decide +kernel)

private theorem bandsAt508 : Checked traceOK 508 512 :=
  Checked.of_segment (lo := 508) (count := 4) (by decide +kernel)

private theorem bandsAt512 : Checked traceOK 512 516 :=
  Checked.of_segment (lo := 512) (count := 4) (by decide +kernel)

private theorem bandsAt516 : Checked traceOK 516 520 :=
  Checked.of_segment (lo := 516) (count := 4) (by decide +kernel)

private theorem bandsAt520 : Checked traceOK 520 524 :=
  Checked.of_segment (lo := 520) (count := 4) (by decide +kernel)

private theorem bandsAt524 : Checked traceOK 524 528 :=
  Checked.of_segment (lo := 524) (count := 4) (by decide +kernel)

private theorem bandsAt528 : Checked traceOK 528 532 :=
  Checked.of_segment (lo := 528) (count := 4) (by decide +kernel)

private theorem bandsAt532 : Checked traceOK 532 536 :=
  Checked.of_segment (lo := 532) (count := 4) (by decide +kernel)

private theorem bandsAt536 : Checked traceOK 536 540 :=
  Checked.of_segment (lo := 536) (count := 4) (by decide +kernel)

private theorem bandsAt540 : Checked traceOK 540 544 :=
  Checked.of_segment (lo := 540) (count := 4) (by decide +kernel)

private theorem bandsAt544 : Checked traceOK 544 548 :=
  Checked.of_segment (lo := 544) (count := 4) (by decide +kernel)

private theorem bandsAt548 : Checked traceOK 548 552 :=
  Checked.of_segment (lo := 548) (count := 4) (by decide +kernel)

private theorem bandsAt552 : Checked traceOK 552 556 :=
  Checked.of_segment (lo := 552) (count := 4) (by decide +kernel)

private theorem bandsAt556 : Checked traceOK 556 560 :=
  Checked.of_segment (lo := 556) (count := 4) (by decide +kernel)

private theorem bandsAt560 : Checked traceOK 560 562 :=
  Checked.of_segment (lo := 560) (count := 2) (by decide +kernel)

theorem bandsFrom500 : Checked traceOK 500 562 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt500 bandsAt504) (Checked.join bandsAt508 bandsAt512)) (Checked.join (Checked.join bandsAt516 bandsAt520) (Checked.join bandsAt524 bandsAt528))) (Checked.join (Checked.join (Checked.join bandsAt532 bandsAt536) (Checked.join bandsAt540 bandsAt544)) (Checked.join (Checked.join bandsAt548 bandsAt552) (Checked.join bandsAt556 bandsAt560))))

private theorem rowsAt8000 : Checked rowOK 8000 8032 :=
  Checked.of_fused_segment (lo := 8000) (count := 32) (by decide +kernel)

private theorem rowsAt8032 : Checked rowOK 8032 8064 :=
  Checked.of_fused_segment (lo := 8032) (count := 32) (by decide +kernel)

private theorem rowsAt8064 : Checked rowOK 8064 8096 :=
  Checked.of_fused_segment (lo := 8064) (count := 32) (by decide +kernel)

private theorem rowsAt8096 : Checked rowOK 8096 8128 :=
  Checked.of_fused_segment (lo := 8096) (count := 32) (by decide +kernel)

private theorem rowsAt8128 : Checked rowOK 8128 8160 :=
  Checked.of_fused_segment (lo := 8128) (count := 32) (by decide +kernel)

private theorem rowsAt8160 : Checked rowOK 8160 8192 :=
  Checked.of_fused_segment (lo := 8160) (count := 32) (by decide +kernel)

private theorem rowsAt8192 : Checked rowOK 8192 8224 :=
  Checked.of_fused_segment (lo := 8192) (count := 32) (by decide +kernel)

private theorem rowsAt8224 : Checked rowOK 8224 8256 :=
  Checked.of_fused_segment (lo := 8224) (count := 32) (by decide +kernel)

private theorem rowsAt8256 : Checked rowOK 8256 8288 :=
  Checked.of_fused_segment (lo := 8256) (count := 32) (by decide +kernel)

private theorem rowsAt8288 : Checked rowOK 8288 8320 :=
  Checked.of_fused_segment (lo := 8288) (count := 32) (by decide +kernel)

private theorem rowsAt8320 : Checked rowOK 8320 8352 :=
  Checked.of_fused_segment (lo := 8320) (count := 32) (by decide +kernel)

private theorem rowsAt8352 : Checked rowOK 8352 8384 :=
  Checked.of_fused_segment (lo := 8352) (count := 32) (by decide +kernel)

private theorem rowsAt8384 : Checked rowOK 8384 8416 :=
  Checked.of_fused_segment (lo := 8384) (count := 32) (by decide +kernel)

private theorem rowsAt8416 : Checked rowOK 8416 8448 :=
  Checked.of_fused_segment (lo := 8416) (count := 32) (by decide +kernel)

private theorem rowsAt8448 : Checked rowOK 8448 8480 :=
  Checked.of_fused_segment (lo := 8448) (count := 32) (by decide +kernel)

private theorem rowsAt8480 : Checked rowOK 8480 8512 :=
  Checked.of_fused_segment (lo := 8480) (count := 32) (by decide +kernel)

private theorem rowsAt8512 : Checked rowOK 8512 8544 :=
  Checked.of_fused_segment (lo := 8512) (count := 32) (by decide +kernel)

private theorem rowsAt8544 : Checked rowOK 8544 8576 :=
  Checked.of_fused_segment (lo := 8544) (count := 32) (by decide +kernel)

private theorem rowsAt8576 : Checked rowOK 8576 8608 :=
  Checked.of_fused_segment (lo := 8576) (count := 32) (by decide +kernel)

private theorem rowsAt8608 : Checked rowOK 8608 8640 :=
  Checked.of_fused_segment (lo := 8608) (count := 32) (by decide +kernel)

private theorem rowsAt8640 : Checked rowOK 8640 8672 :=
  Checked.of_fused_segment (lo := 8640) (count := 32) (by decide +kernel)

private theorem rowsAt8672 : Checked rowOK 8672 8704 :=
  Checked.of_fused_segment (lo := 8672) (count := 32) (by decide +kernel)

private theorem rowsAt8704 : Checked rowOK 8704 8736 :=
  Checked.of_fused_segment (lo := 8704) (count := 32) (by decide +kernel)

private theorem rowsAt8736 : Checked rowOK 8736 8768 :=
  Checked.of_fused_segment (lo := 8736) (count := 32) (by decide +kernel)

private theorem rowsAt8768 : Checked rowOK 8768 8800 :=
  Checked.of_fused_segment (lo := 8768) (count := 32) (by decide +kernel)

private theorem rowsAt8800 : Checked rowOK 8800 8832 :=
  Checked.of_fused_segment (lo := 8800) (count := 32) (by decide +kernel)

private theorem rowsAt8832 : Checked rowOK 8832 8864 :=
  Checked.of_fused_segment (lo := 8832) (count := 32) (by decide +kernel)

private theorem rowsAt8864 : Checked rowOK 8864 8896 :=
  Checked.of_fused_segment (lo := 8864) (count := 32) (by decide +kernel)

private theorem rowsAt8896 : Checked rowOK 8896 8928 :=
  Checked.of_fused_segment (lo := 8896) (count := 32) (by decide +kernel)

private theorem rowsAt8928 : Checked rowOK 8928 8960 :=
  Checked.of_fused_segment (lo := 8928) (count := 32) (by decide +kernel)

private theorem rowsAt8960 : Checked rowOK 8960 8992 :=
  Checked.of_fused_segment (lo := 8960) (count := 32) (by decide +kernel)

private theorem rowsAt8992 : Checked rowOK 8992 9000 :=
  Checked.of_fused_segment (lo := 8992) (count := 8) (by decide +kernel)

theorem rowsFrom8000 : Checked rowOK 8000 9000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt8000 rowsAt8032) (Checked.join rowsAt8064 rowsAt8096)) (Checked.join (Checked.join rowsAt8128 rowsAt8160) (Checked.join rowsAt8192 rowsAt8224))) (Checked.join (Checked.join (Checked.join rowsAt8256 rowsAt8288) (Checked.join rowsAt8320 rowsAt8352)) (Checked.join (Checked.join rowsAt8384 rowsAt8416) (Checked.join rowsAt8448 rowsAt8480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt8512 rowsAt8544) (Checked.join rowsAt8576 rowsAt8608)) (Checked.join (Checked.join rowsAt8640 rowsAt8672) (Checked.join rowsAt8704 rowsAt8736))) (Checked.join (Checked.join (Checked.join rowsAt8768 rowsAt8800) (Checked.join rowsAt8832 rowsAt8864)) (Checked.join (Checked.join rowsAt8896 rowsAt8928) (Checked.join rowsAt8960 rowsAt8992)))))

end GaussianChains.Point22.Atlas.Tables
