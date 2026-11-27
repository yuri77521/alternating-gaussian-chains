import Point22AtlasTablesPart15

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt1000 : Checked traceOK 1000 1004 :=
  Checked.of_segment (lo := 1000) (count := 4) (by decide +kernel)

private theorem bandsAt1004 : Checked traceOK 1004 1008 :=
  Checked.of_segment (lo := 1004) (count := 4) (by decide +kernel)

private theorem bandsAt1008 : Checked traceOK 1008 1012 :=
  Checked.of_segment (lo := 1008) (count := 4) (by decide +kernel)

private theorem bandsAt1012 : Checked traceOK 1012 1016 :=
  Checked.of_segment (lo := 1012) (count := 4) (by decide +kernel)

private theorem bandsAt1016 : Checked traceOK 1016 1020 :=
  Checked.of_segment (lo := 1016) (count := 4) (by decide +kernel)

private theorem bandsAt1020 : Checked traceOK 1020 1024 :=
  Checked.of_segment (lo := 1020) (count := 4) (by decide +kernel)

private theorem bandsAt1024 : Checked traceOK 1024 1028 :=
  Checked.of_segment (lo := 1024) (count := 4) (by decide +kernel)

private theorem bandsAt1028 : Checked traceOK 1028 1032 :=
  Checked.of_segment (lo := 1028) (count := 4) (by decide +kernel)

private theorem bandsAt1032 : Checked traceOK 1032 1036 :=
  Checked.of_segment (lo := 1032) (count := 4) (by decide +kernel)

private theorem bandsAt1036 : Checked traceOK 1036 1040 :=
  Checked.of_segment (lo := 1036) (count := 4) (by decide +kernel)

private theorem bandsAt1040 : Checked traceOK 1040 1044 :=
  Checked.of_segment (lo := 1040) (count := 4) (by decide +kernel)

private theorem bandsAt1044 : Checked traceOK 1044 1048 :=
  Checked.of_segment (lo := 1044) (count := 4) (by decide +kernel)

private theorem bandsAt1048 : Checked traceOK 1048 1052 :=
  Checked.of_segment (lo := 1048) (count := 4) (by decide +kernel)

private theorem bandsAt1052 : Checked traceOK 1052 1056 :=
  Checked.of_segment (lo := 1052) (count := 4) (by decide +kernel)

private theorem bandsAt1056 : Checked traceOK 1056 1060 :=
  Checked.of_segment (lo := 1056) (count := 4) (by decide +kernel)

private theorem bandsAt1060 : Checked traceOK 1060 1062 :=
  Checked.of_segment (lo := 1060) (count := 2) (by decide +kernel)

theorem bandsFrom1000 : Checked traceOK 1000 1062 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt1000 bandsAt1004) (Checked.join bandsAt1008 bandsAt1012)) (Checked.join (Checked.join bandsAt1016 bandsAt1020) (Checked.join bandsAt1024 bandsAt1028))) (Checked.join (Checked.join (Checked.join bandsAt1032 bandsAt1036) (Checked.join bandsAt1040 bandsAt1044)) (Checked.join (Checked.join bandsAt1048 bandsAt1052) (Checked.join bandsAt1056 bandsAt1060))))

private theorem rowsAt16000 : Checked rowOK 16000 16032 :=
  Checked.of_fused_segment (lo := 16000) (count := 32) (by decide +kernel)

private theorem rowsAt16032 : Checked rowOK 16032 16064 :=
  Checked.of_fused_segment (lo := 16032) (count := 32) (by decide +kernel)

private theorem rowsAt16064 : Checked rowOK 16064 16096 :=
  Checked.of_fused_segment (lo := 16064) (count := 32) (by decide +kernel)

private theorem rowsAt16096 : Checked rowOK 16096 16128 :=
  Checked.of_fused_segment (lo := 16096) (count := 32) (by decide +kernel)

private theorem rowsAt16128 : Checked rowOK 16128 16160 :=
  Checked.of_fused_segment (lo := 16128) (count := 32) (by decide +kernel)

private theorem rowsAt16160 : Checked rowOK 16160 16192 :=
  Checked.of_fused_segment (lo := 16160) (count := 32) (by decide +kernel)

private theorem rowsAt16192 : Checked rowOK 16192 16224 :=
  Checked.of_fused_segment (lo := 16192) (count := 32) (by decide +kernel)

private theorem rowsAt16224 : Checked rowOK 16224 16256 :=
  Checked.of_fused_segment (lo := 16224) (count := 32) (by decide +kernel)

private theorem rowsAt16256 : Checked rowOK 16256 16288 :=
  Checked.of_fused_segment (lo := 16256) (count := 32) (by decide +kernel)

private theorem rowsAt16288 : Checked rowOK 16288 16320 :=
  Checked.of_fused_segment (lo := 16288) (count := 32) (by decide +kernel)

private theorem rowsAt16320 : Checked rowOK 16320 16352 :=
  Checked.of_fused_segment (lo := 16320) (count := 32) (by decide +kernel)

private theorem rowsAt16352 : Checked rowOK 16352 16384 :=
  Checked.of_fused_segment (lo := 16352) (count := 32) (by decide +kernel)

private theorem rowsAt16384 : Checked rowOK 16384 16416 :=
  Checked.of_fused_segment (lo := 16384) (count := 32) (by decide +kernel)

private theorem rowsAt16416 : Checked rowOK 16416 16448 :=
  Checked.of_fused_segment (lo := 16416) (count := 32) (by decide +kernel)

private theorem rowsAt16448 : Checked rowOK 16448 16480 :=
  Checked.of_fused_segment (lo := 16448) (count := 32) (by decide +kernel)

private theorem rowsAt16480 : Checked rowOK 16480 16512 :=
  Checked.of_fused_segment (lo := 16480) (count := 32) (by decide +kernel)

private theorem rowsAt16512 : Checked rowOK 16512 16544 :=
  Checked.of_fused_segment (lo := 16512) (count := 32) (by decide +kernel)

private theorem rowsAt16544 : Checked rowOK 16544 16576 :=
  Checked.of_fused_segment (lo := 16544) (count := 32) (by decide +kernel)

private theorem rowsAt16576 : Checked rowOK 16576 16608 :=
  Checked.of_fused_segment (lo := 16576) (count := 32) (by decide +kernel)

private theorem rowsAt16608 : Checked rowOK 16608 16640 :=
  Checked.of_fused_segment (lo := 16608) (count := 32) (by decide +kernel)

private theorem rowsAt16640 : Checked rowOK 16640 16672 :=
  Checked.of_fused_segment (lo := 16640) (count := 32) (by decide +kernel)

private theorem rowsAt16672 : Checked rowOK 16672 16704 :=
  Checked.of_fused_segment (lo := 16672) (count := 32) (by decide +kernel)

private theorem rowsAt16704 : Checked rowOK 16704 16736 :=
  Checked.of_fused_segment (lo := 16704) (count := 32) (by decide +kernel)

private theorem rowsAt16736 : Checked rowOK 16736 16768 :=
  Checked.of_fused_segment (lo := 16736) (count := 32) (by decide +kernel)

private theorem rowsAt16768 : Checked rowOK 16768 16800 :=
  Checked.of_fused_segment (lo := 16768) (count := 32) (by decide +kernel)

private theorem rowsAt16800 : Checked rowOK 16800 16832 :=
  Checked.of_fused_segment (lo := 16800) (count := 32) (by decide +kernel)

private theorem rowsAt16832 : Checked rowOK 16832 16864 :=
  Checked.of_fused_segment (lo := 16832) (count := 32) (by decide +kernel)

private theorem rowsAt16864 : Checked rowOK 16864 16896 :=
  Checked.of_fused_segment (lo := 16864) (count := 32) (by decide +kernel)

private theorem rowsAt16896 : Checked rowOK 16896 16928 :=
  Checked.of_fused_segment (lo := 16896) (count := 32) (by decide +kernel)

private theorem rowsAt16928 : Checked rowOK 16928 16960 :=
  Checked.of_fused_segment (lo := 16928) (count := 32) (by decide +kernel)

private theorem rowsAt16960 : Checked rowOK 16960 16992 :=
  Checked.of_fused_segment (lo := 16960) (count := 32) (by decide +kernel)

private theorem rowsAt16992 : Checked rowOK 16992 17000 :=
  Checked.of_fused_segment (lo := 16992) (count := 8) (by decide +kernel)

theorem rowsFrom16000 : Checked rowOK 16000 17000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt16000 rowsAt16032) (Checked.join rowsAt16064 rowsAt16096)) (Checked.join (Checked.join rowsAt16128 rowsAt16160) (Checked.join rowsAt16192 rowsAt16224))) (Checked.join (Checked.join (Checked.join rowsAt16256 rowsAt16288) (Checked.join rowsAt16320 rowsAt16352)) (Checked.join (Checked.join rowsAt16384 rowsAt16416) (Checked.join rowsAt16448 rowsAt16480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt16512 rowsAt16544) (Checked.join rowsAt16576 rowsAt16608)) (Checked.join (Checked.join rowsAt16640 rowsAt16672) (Checked.join rowsAt16704 rowsAt16736))) (Checked.join (Checked.join (Checked.join rowsAt16768 rowsAt16800) (Checked.join rowsAt16832 rowsAt16864)) (Checked.join (Checked.join rowsAt16896 rowsAt16928) (Checked.join rowsAt16960 rowsAt16992)))))

end GaussianChains.Point22.Atlas.Tables
