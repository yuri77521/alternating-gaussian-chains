import Point22AtlasTablesPart03

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt250 : Checked traceOK 250 254 :=
  Checked.of_segment (lo := 250) (count := 4) (by decide +kernel)

private theorem bandsAt254 : Checked traceOK 254 258 :=
  Checked.of_segment (lo := 254) (count := 4) (by decide +kernel)

private theorem bandsAt258 : Checked traceOK 258 262 :=
  Checked.of_segment (lo := 258) (count := 4) (by decide +kernel)

private theorem bandsAt262 : Checked traceOK 262 266 :=
  Checked.of_segment (lo := 262) (count := 4) (by decide +kernel)

private theorem bandsAt266 : Checked traceOK 266 270 :=
  Checked.of_segment (lo := 266) (count := 4) (by decide +kernel)

private theorem bandsAt270 : Checked traceOK 270 274 :=
  Checked.of_segment (lo := 270) (count := 4) (by decide +kernel)

private theorem bandsAt274 : Checked traceOK 274 278 :=
  Checked.of_segment (lo := 274) (count := 4) (by decide +kernel)

private theorem bandsAt278 : Checked traceOK 278 282 :=
  Checked.of_segment (lo := 278) (count := 4) (by decide +kernel)

private theorem bandsAt282 : Checked traceOK 282 286 :=
  Checked.of_segment (lo := 282) (count := 4) (by decide +kernel)

private theorem bandsAt286 : Checked traceOK 286 290 :=
  Checked.of_segment (lo := 286) (count := 4) (by decide +kernel)

private theorem bandsAt290 : Checked traceOK 290 294 :=
  Checked.of_segment (lo := 290) (count := 4) (by decide +kernel)

private theorem bandsAt294 : Checked traceOK 294 298 :=
  Checked.of_segment (lo := 294) (count := 4) (by decide +kernel)

private theorem bandsAt298 : Checked traceOK 298 302 :=
  Checked.of_segment (lo := 298) (count := 4) (by decide +kernel)

private theorem bandsAt302 : Checked traceOK 302 306 :=
  Checked.of_segment (lo := 302) (count := 4) (by decide +kernel)

private theorem bandsAt306 : Checked traceOK 306 310 :=
  Checked.of_segment (lo := 306) (count := 4) (by decide +kernel)

private theorem bandsAt310 : Checked traceOK 310 312 :=
  Checked.of_segment (lo := 310) (count := 2) (by decide +kernel)

theorem bandsFrom250 : Checked traceOK 250 312 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt250 bandsAt254) (Checked.join bandsAt258 bandsAt262)) (Checked.join (Checked.join bandsAt266 bandsAt270) (Checked.join bandsAt274 bandsAt278))) (Checked.join (Checked.join (Checked.join bandsAt282 bandsAt286) (Checked.join bandsAt290 bandsAt294)) (Checked.join (Checked.join bandsAt298 bandsAt302) (Checked.join bandsAt306 bandsAt310))))

private theorem rowsAt4000 : Checked rowOK 4000 4032 :=
  Checked.of_segment (lo := 4000) (count := 32) (by decide +kernel)

private theorem rowsAt4032 : Checked rowOK 4032 4064 :=
  Checked.of_segment (lo := 4032) (count := 32) (by decide +kernel)

private theorem rowsAt4064 : Checked rowOK 4064 4096 :=
  Checked.of_segment (lo := 4064) (count := 32) (by decide +kernel)

private theorem rowsAt4096 : Checked rowOK 4096 4128 :=
  Checked.of_segment (lo := 4096) (count := 32) (by decide +kernel)

private theorem rowsAt4128 : Checked rowOK 4128 4160 :=
  Checked.of_segment (lo := 4128) (count := 32) (by decide +kernel)

private theorem rowsAt4160 : Checked rowOK 4160 4192 :=
  Checked.of_segment (lo := 4160) (count := 32) (by decide +kernel)

private theorem rowsAt4192 : Checked rowOK 4192 4224 :=
  Checked.of_segment (lo := 4192) (count := 32) (by decide +kernel)

private theorem rowsAt4224 : Checked rowOK 4224 4256 :=
  Checked.of_segment (lo := 4224) (count := 32) (by decide +kernel)

private theorem rowsAt4256 : Checked rowOK 4256 4288 :=
  Checked.of_segment (lo := 4256) (count := 32) (by decide +kernel)

private theorem rowsAt4288 : Checked rowOK 4288 4320 :=
  Checked.of_segment (lo := 4288) (count := 32) (by decide +kernel)

private theorem rowsAt4320 : Checked rowOK 4320 4352 :=
  Checked.of_segment (lo := 4320) (count := 32) (by decide +kernel)

private theorem rowsAt4352 : Checked rowOK 4352 4384 :=
  Checked.of_segment (lo := 4352) (count := 32) (by decide +kernel)

private theorem rowsAt4384 : Checked rowOK 4384 4416 :=
  Checked.of_segment (lo := 4384) (count := 32) (by decide +kernel)

private theorem rowsAt4416 : Checked rowOK 4416 4448 :=
  Checked.of_segment (lo := 4416) (count := 32) (by decide +kernel)

private theorem rowsAt4448 : Checked rowOK 4448 4480 :=
  Checked.of_segment (lo := 4448) (count := 32) (by decide +kernel)

private theorem rowsAt4480 : Checked rowOK 4480 4512 :=
  Checked.of_segment (lo := 4480) (count := 32) (by decide +kernel)

private theorem rowsAt4512 : Checked rowOK 4512 4544 :=
  Checked.of_segment (lo := 4512) (count := 32) (by decide +kernel)

private theorem rowsAt4544 : Checked rowOK 4544 4576 :=
  Checked.of_segment (lo := 4544) (count := 32) (by decide +kernel)

private theorem rowsAt4576 : Checked rowOK 4576 4608 :=
  Checked.of_segment (lo := 4576) (count := 32) (by decide +kernel)

private theorem rowsAt4608 : Checked rowOK 4608 4640 :=
  Checked.of_segment (lo := 4608) (count := 32) (by decide +kernel)

private theorem rowsAt4640 : Checked rowOK 4640 4672 :=
  Checked.of_segment (lo := 4640) (count := 32) (by decide +kernel)

private theorem rowsAt4672 : Checked rowOK 4672 4704 :=
  Checked.of_segment (lo := 4672) (count := 32) (by decide +kernel)

private theorem rowsAt4704 : Checked rowOK 4704 4736 :=
  Checked.of_segment (lo := 4704) (count := 32) (by decide +kernel)

private theorem rowsAt4736 : Checked rowOK 4736 4768 :=
  Checked.of_segment (lo := 4736) (count := 32) (by decide +kernel)

private theorem rowsAt4768 : Checked rowOK 4768 4800 :=
  Checked.of_segment (lo := 4768) (count := 32) (by decide +kernel)

private theorem rowsAt4800 : Checked rowOK 4800 4832 :=
  Checked.of_segment (lo := 4800) (count := 32) (by decide +kernel)

private theorem rowsAt4832 : Checked rowOK 4832 4864 :=
  Checked.of_segment (lo := 4832) (count := 32) (by decide +kernel)

private theorem rowsAt4864 : Checked rowOK 4864 4896 :=
  Checked.of_segment (lo := 4864) (count := 32) (by decide +kernel)

private theorem rowsAt4896 : Checked rowOK 4896 4928 :=
  Checked.of_segment (lo := 4896) (count := 32) (by decide +kernel)

private theorem rowsAt4928 : Checked rowOK 4928 4960 :=
  Checked.of_segment (lo := 4928) (count := 32) (by decide +kernel)

private theorem rowsAt4960 : Checked rowOK 4960 4992 :=
  Checked.of_segment (lo := 4960) (count := 32) (by decide +kernel)

private theorem rowsAt4992 : Checked rowOK 4992 5000 :=
  Checked.of_segment (lo := 4992) (count := 8) (by decide +kernel)

theorem rowsFrom4000 : Checked rowOK 4000 5000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt4000 rowsAt4032) (Checked.join rowsAt4064 rowsAt4096)) (Checked.join (Checked.join rowsAt4128 rowsAt4160) (Checked.join rowsAt4192 rowsAt4224))) (Checked.join (Checked.join (Checked.join rowsAt4256 rowsAt4288) (Checked.join rowsAt4320 rowsAt4352)) (Checked.join (Checked.join rowsAt4384 rowsAt4416) (Checked.join rowsAt4448 rowsAt4480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt4512 rowsAt4544) (Checked.join rowsAt4576 rowsAt4608)) (Checked.join (Checked.join rowsAt4640 rowsAt4672) (Checked.join rowsAt4704 rowsAt4736))) (Checked.join (Checked.join (Checked.join rowsAt4768 rowsAt4800) (Checked.join rowsAt4832 rowsAt4864)) (Checked.join (Checked.join rowsAt4896 rowsAt4928) (Checked.join rowsAt4960 rowsAt4992)))))

end GaussianChains.Point22.Atlas.Tables
