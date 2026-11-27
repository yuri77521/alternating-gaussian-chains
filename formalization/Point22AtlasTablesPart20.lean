import Point22AtlasTablesPart19

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt1250 : Checked traceOK 1250 1254 :=
  Checked.of_segment (lo := 1250) (count := 4) (by decide +kernel)

private theorem bandsAt1254 : Checked traceOK 1254 1258 :=
  Checked.of_segment (lo := 1254) (count := 4) (by decide +kernel)

private theorem bandsAt1258 : Checked traceOK 1258 1262 :=
  Checked.of_segment (lo := 1258) (count := 4) (by decide +kernel)

private theorem bandsAt1262 : Checked traceOK 1262 1266 :=
  Checked.of_segment (lo := 1262) (count := 4) (by decide +kernel)

private theorem bandsAt1266 : Checked traceOK 1266 1270 :=
  Checked.of_segment (lo := 1266) (count := 4) (by decide +kernel)

private theorem bandsAt1270 : Checked traceOK 1270 1274 :=
  Checked.of_segment (lo := 1270) (count := 4) (by decide +kernel)

private theorem bandsAt1274 : Checked traceOK 1274 1278 :=
  Checked.of_segment (lo := 1274) (count := 4) (by decide +kernel)

private theorem bandsAt1278 : Checked traceOK 1278 1282 :=
  Checked.of_segment (lo := 1278) (count := 4) (by decide +kernel)

private theorem bandsAt1282 : Checked traceOK 1282 1286 :=
  Checked.of_segment (lo := 1282) (count := 4) (by decide +kernel)

private theorem bandsAt1286 : Checked traceOK 1286 1290 :=
  Checked.of_segment (lo := 1286) (count := 4) (by decide +kernel)

private theorem bandsAt1290 : Checked traceOK 1290 1294 :=
  Checked.of_segment (lo := 1290) (count := 4) (by decide +kernel)

private theorem bandsAt1294 : Checked traceOK 1294 1298 :=
  Checked.of_segment (lo := 1294) (count := 4) (by decide +kernel)

private theorem bandsAt1298 : Checked traceOK 1298 1302 :=
  Checked.of_segment (lo := 1298) (count := 4) (by decide +kernel)

private theorem bandsAt1302 : Checked traceOK 1302 1306 :=
  Checked.of_segment (lo := 1302) (count := 4) (by decide +kernel)

private theorem bandsAt1306 : Checked traceOK 1306 1310 :=
  Checked.of_segment (lo := 1306) (count := 4) (by decide +kernel)

private theorem bandsAt1310 : Checked traceOK 1310 1312 :=
  Checked.of_segment (lo := 1310) (count := 2) (by decide +kernel)

theorem bandsFrom1250 : Checked traceOK 1250 1312 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt1250 bandsAt1254) (Checked.join bandsAt1258 bandsAt1262)) (Checked.join (Checked.join bandsAt1266 bandsAt1270) (Checked.join bandsAt1274 bandsAt1278))) (Checked.join (Checked.join (Checked.join bandsAt1282 bandsAt1286) (Checked.join bandsAt1290 bandsAt1294)) (Checked.join (Checked.join bandsAt1298 bandsAt1302) (Checked.join bandsAt1306 bandsAt1310))))

private theorem rowsAt20000 : Checked rowOK 20000 20032 :=
  Checked.of_fused_segment (lo := 20000) (count := 32) (by decide +kernel)

private theorem rowsAt20032 : Checked rowOK 20032 20064 :=
  Checked.of_fused_segment (lo := 20032) (count := 32) (by decide +kernel)

private theorem rowsAt20064 : Checked rowOK 20064 20096 :=
  Checked.of_fused_segment (lo := 20064) (count := 32) (by decide +kernel)

private theorem rowsAt20096 : Checked rowOK 20096 20128 :=
  Checked.of_fused_segment (lo := 20096) (count := 32) (by decide +kernel)

private theorem rowsAt20128 : Checked rowOK 20128 20160 :=
  Checked.of_fused_segment (lo := 20128) (count := 32) (by decide +kernel)

private theorem rowsAt20160 : Checked rowOK 20160 20192 :=
  Checked.of_fused_segment (lo := 20160) (count := 32) (by decide +kernel)

private theorem rowsAt20192 : Checked rowOK 20192 20224 :=
  Checked.of_fused_segment (lo := 20192) (count := 32) (by decide +kernel)

private theorem rowsAt20224 : Checked rowOK 20224 20256 :=
  Checked.of_fused_segment (lo := 20224) (count := 32) (by decide +kernel)

private theorem rowsAt20256 : Checked rowOK 20256 20288 :=
  Checked.of_fused_segment (lo := 20256) (count := 32) (by decide +kernel)

private theorem rowsAt20288 : Checked rowOK 20288 20320 :=
  Checked.of_fused_segment (lo := 20288) (count := 32) (by decide +kernel)

private theorem rowsAt20320 : Checked rowOK 20320 20352 :=
  Checked.of_fused_segment (lo := 20320) (count := 32) (by decide +kernel)

private theorem rowsAt20352 : Checked rowOK 20352 20384 :=
  Checked.of_fused_segment (lo := 20352) (count := 32) (by decide +kernel)

private theorem rowsAt20384 : Checked rowOK 20384 20416 :=
  Checked.of_fused_segment (lo := 20384) (count := 32) (by decide +kernel)

private theorem rowsAt20416 : Checked rowOK 20416 20448 :=
  Checked.of_fused_segment (lo := 20416) (count := 32) (by decide +kernel)

private theorem rowsAt20448 : Checked rowOK 20448 20480 :=
  Checked.of_fused_segment (lo := 20448) (count := 32) (by decide +kernel)

private theorem rowsAt20480 : Checked rowOK 20480 20512 :=
  Checked.of_fused_segment (lo := 20480) (count := 32) (by decide +kernel)

private theorem rowsAt20512 : Checked rowOK 20512 20544 :=
  Checked.of_fused_segment (lo := 20512) (count := 32) (by decide +kernel)

private theorem rowsAt20544 : Checked rowOK 20544 20576 :=
  Checked.of_fused_segment (lo := 20544) (count := 32) (by decide +kernel)

private theorem rowsAt20576 : Checked rowOK 20576 20608 :=
  Checked.of_fused_segment (lo := 20576) (count := 32) (by decide +kernel)

private theorem rowsAt20608 : Checked rowOK 20608 20640 :=
  Checked.of_fused_segment (lo := 20608) (count := 32) (by decide +kernel)

private theorem rowsAt20640 : Checked rowOK 20640 20672 :=
  Checked.of_fused_segment (lo := 20640) (count := 32) (by decide +kernel)

private theorem rowsAt20672 : Checked rowOK 20672 20704 :=
  Checked.of_fused_segment (lo := 20672) (count := 32) (by decide +kernel)

private theorem rowsAt20704 : Checked rowOK 20704 20736 :=
  Checked.of_fused_segment (lo := 20704) (count := 32) (by decide +kernel)

private theorem rowsAt20736 : Checked rowOK 20736 20768 :=
  Checked.of_fused_segment (lo := 20736) (count := 32) (by decide +kernel)

private theorem rowsAt20768 : Checked rowOK 20768 20800 :=
  Checked.of_fused_segment (lo := 20768) (count := 32) (by decide +kernel)

private theorem rowsAt20800 : Checked rowOK 20800 20832 :=
  Checked.of_fused_segment (lo := 20800) (count := 32) (by decide +kernel)

private theorem rowsAt20832 : Checked rowOK 20832 20864 :=
  Checked.of_fused_segment (lo := 20832) (count := 32) (by decide +kernel)

private theorem rowsAt20864 : Checked rowOK 20864 20896 :=
  Checked.of_fused_segment (lo := 20864) (count := 32) (by decide +kernel)

private theorem rowsAt20896 : Checked rowOK 20896 20928 :=
  Checked.of_fused_segment (lo := 20896) (count := 32) (by decide +kernel)

private theorem rowsAt20928 : Checked rowOK 20928 20960 :=
  Checked.of_fused_segment (lo := 20928) (count := 32) (by decide +kernel)

private theorem rowsAt20960 : Checked rowOK 20960 20992 :=
  Checked.of_fused_segment (lo := 20960) (count := 32) (by decide +kernel)

private theorem rowsAt20992 : Checked rowOK 20992 21000 :=
  Checked.of_fused_segment (lo := 20992) (count := 8) (by decide +kernel)

theorem rowsFrom20000 : Checked rowOK 20000 21000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt20000 rowsAt20032) (Checked.join rowsAt20064 rowsAt20096)) (Checked.join (Checked.join rowsAt20128 rowsAt20160) (Checked.join rowsAt20192 rowsAt20224))) (Checked.join (Checked.join (Checked.join rowsAt20256 rowsAt20288) (Checked.join rowsAt20320 rowsAt20352)) (Checked.join (Checked.join rowsAt20384 rowsAt20416) (Checked.join rowsAt20448 rowsAt20480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt20512 rowsAt20544) (Checked.join rowsAt20576 rowsAt20608)) (Checked.join (Checked.join rowsAt20640 rowsAt20672) (Checked.join rowsAt20704 rowsAt20736))) (Checked.join (Checked.join (Checked.join rowsAt20768 rowsAt20800) (Checked.join rowsAt20832 rowsAt20864)) (Checked.join (Checked.join rowsAt20896 rowsAt20928) (Checked.join rowsAt20960 rowsAt20992)))))

end GaussianChains.Point22.Atlas.Tables
