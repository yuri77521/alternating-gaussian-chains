import Point22AtlasTablesPart02

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt187 : Checked traceOK 187 191 :=
  Checked.of_segment (lo := 187) (count := 4) (by decide +kernel)

private theorem bandsAt191 : Checked traceOK 191 195 :=
  Checked.of_segment (lo := 191) (count := 4) (by decide +kernel)

private theorem bandsAt195 : Checked traceOK 195 199 :=
  Checked.of_segment (lo := 195) (count := 4) (by decide +kernel)

private theorem bandsAt199 : Checked traceOK 199 203 :=
  Checked.of_segment (lo := 199) (count := 4) (by decide +kernel)

private theorem bandsAt203 : Checked traceOK 203 207 :=
  Checked.of_segment (lo := 203) (count := 4) (by decide +kernel)

private theorem bandsAt207 : Checked traceOK 207 211 :=
  Checked.of_segment (lo := 207) (count := 4) (by decide +kernel)

private theorem bandsAt211 : Checked traceOK 211 215 :=
  Checked.of_segment (lo := 211) (count := 4) (by decide +kernel)

private theorem bandsAt215 : Checked traceOK 215 219 :=
  Checked.of_segment (lo := 215) (count := 4) (by decide +kernel)

private theorem bandsAt219 : Checked traceOK 219 223 :=
  Checked.of_segment (lo := 219) (count := 4) (by decide +kernel)

private theorem bandsAt223 : Checked traceOK 223 227 :=
  Checked.of_segment (lo := 223) (count := 4) (by decide +kernel)

private theorem bandsAt227 : Checked traceOK 227 231 :=
  Checked.of_segment (lo := 227) (count := 4) (by decide +kernel)

private theorem bandsAt231 : Checked traceOK 231 235 :=
  Checked.of_segment (lo := 231) (count := 4) (by decide +kernel)

private theorem bandsAt235 : Checked traceOK 235 239 :=
  Checked.of_segment (lo := 235) (count := 4) (by decide +kernel)

private theorem bandsAt239 : Checked traceOK 239 243 :=
  Checked.of_segment (lo := 239) (count := 4) (by decide +kernel)

private theorem bandsAt243 : Checked traceOK 243 247 :=
  Checked.of_segment (lo := 243) (count := 4) (by decide +kernel)

private theorem bandsAt247 : Checked traceOK 247 250 :=
  Checked.of_segment (lo := 247) (count := 3) (by decide +kernel)

theorem bandsFrom187 : Checked traceOK 187 250 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt187 bandsAt191) (Checked.join bandsAt195 bandsAt199)) (Checked.join (Checked.join bandsAt203 bandsAt207) (Checked.join bandsAt211 bandsAt215))) (Checked.join (Checked.join (Checked.join bandsAt219 bandsAt223) (Checked.join bandsAt227 bandsAt231)) (Checked.join (Checked.join bandsAt235 bandsAt239) (Checked.join bandsAt243 bandsAt247))))

private theorem rowsAt3000 : Checked rowOK 3000 3032 :=
  Checked.of_segment (lo := 3000) (count := 32) (by decide +kernel)

private theorem rowsAt3032 : Checked rowOK 3032 3064 :=
  Checked.of_segment (lo := 3032) (count := 32) (by decide +kernel)

private theorem rowsAt3064 : Checked rowOK 3064 3096 :=
  Checked.of_segment (lo := 3064) (count := 32) (by decide +kernel)

private theorem rowsAt3096 : Checked rowOK 3096 3128 :=
  Checked.of_segment (lo := 3096) (count := 32) (by decide +kernel)

private theorem rowsAt3128 : Checked rowOK 3128 3160 :=
  Checked.of_segment (lo := 3128) (count := 32) (by decide +kernel)

private theorem rowsAt3160 : Checked rowOK 3160 3192 :=
  Checked.of_segment (lo := 3160) (count := 32) (by decide +kernel)

private theorem rowsAt3192 : Checked rowOK 3192 3224 :=
  Checked.of_segment (lo := 3192) (count := 32) (by decide +kernel)

private theorem rowsAt3224 : Checked rowOK 3224 3256 :=
  Checked.of_segment (lo := 3224) (count := 32) (by decide +kernel)

private theorem rowsAt3256 : Checked rowOK 3256 3288 :=
  Checked.of_segment (lo := 3256) (count := 32) (by decide +kernel)

private theorem rowsAt3288 : Checked rowOK 3288 3320 :=
  Checked.of_segment (lo := 3288) (count := 32) (by decide +kernel)

private theorem rowsAt3320 : Checked rowOK 3320 3352 :=
  Checked.of_segment (lo := 3320) (count := 32) (by decide +kernel)

private theorem rowsAt3352 : Checked rowOK 3352 3384 :=
  Checked.of_segment (lo := 3352) (count := 32) (by decide +kernel)

private theorem rowsAt3384 : Checked rowOK 3384 3416 :=
  Checked.of_segment (lo := 3384) (count := 32) (by decide +kernel)

private theorem rowsAt3416 : Checked rowOK 3416 3448 :=
  Checked.of_segment (lo := 3416) (count := 32) (by decide +kernel)

private theorem rowsAt3448 : Checked rowOK 3448 3480 :=
  Checked.of_segment (lo := 3448) (count := 32) (by decide +kernel)

private theorem rowsAt3480 : Checked rowOK 3480 3512 :=
  Checked.of_segment (lo := 3480) (count := 32) (by decide +kernel)

private theorem rowsAt3512 : Checked rowOK 3512 3544 :=
  Checked.of_segment (lo := 3512) (count := 32) (by decide +kernel)

private theorem rowsAt3544 : Checked rowOK 3544 3576 :=
  Checked.of_segment (lo := 3544) (count := 32) (by decide +kernel)

private theorem rowsAt3576 : Checked rowOK 3576 3608 :=
  Checked.of_segment (lo := 3576) (count := 32) (by decide +kernel)

private theorem rowsAt3608 : Checked rowOK 3608 3640 :=
  Checked.of_segment (lo := 3608) (count := 32) (by decide +kernel)

private theorem rowsAt3640 : Checked rowOK 3640 3672 :=
  Checked.of_segment (lo := 3640) (count := 32) (by decide +kernel)

private theorem rowsAt3672 : Checked rowOK 3672 3704 :=
  Checked.of_segment (lo := 3672) (count := 32) (by decide +kernel)

private theorem rowsAt3704 : Checked rowOK 3704 3736 :=
  Checked.of_segment (lo := 3704) (count := 32) (by decide +kernel)

private theorem rowsAt3736 : Checked rowOK 3736 3768 :=
  Checked.of_segment (lo := 3736) (count := 32) (by decide +kernel)

private theorem rowsAt3768 : Checked rowOK 3768 3800 :=
  Checked.of_segment (lo := 3768) (count := 32) (by decide +kernel)

private theorem rowsAt3800 : Checked rowOK 3800 3832 :=
  Checked.of_segment (lo := 3800) (count := 32) (by decide +kernel)

private theorem rowsAt3832 : Checked rowOK 3832 3864 :=
  Checked.of_segment (lo := 3832) (count := 32) (by decide +kernel)

private theorem rowsAt3864 : Checked rowOK 3864 3896 :=
  Checked.of_segment (lo := 3864) (count := 32) (by decide +kernel)

private theorem rowsAt3896 : Checked rowOK 3896 3928 :=
  Checked.of_segment (lo := 3896) (count := 32) (by decide +kernel)

private theorem rowsAt3928 : Checked rowOK 3928 3960 :=
  Checked.of_segment (lo := 3928) (count := 32) (by decide +kernel)

private theorem rowsAt3960 : Checked rowOK 3960 3992 :=
  Checked.of_segment (lo := 3960) (count := 32) (by decide +kernel)

private theorem rowsAt3992 : Checked rowOK 3992 4000 :=
  Checked.of_segment (lo := 3992) (count := 8) (by decide +kernel)

theorem rowsFrom3000 : Checked rowOK 3000 4000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt3000 rowsAt3032) (Checked.join rowsAt3064 rowsAt3096)) (Checked.join (Checked.join rowsAt3128 rowsAt3160) (Checked.join rowsAt3192 rowsAt3224))) (Checked.join (Checked.join (Checked.join rowsAt3256 rowsAt3288) (Checked.join rowsAt3320 rowsAt3352)) (Checked.join (Checked.join rowsAt3384 rowsAt3416) (Checked.join rowsAt3448 rowsAt3480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt3512 rowsAt3544) (Checked.join rowsAt3576 rowsAt3608)) (Checked.join (Checked.join rowsAt3640 rowsAt3672) (Checked.join rowsAt3704 rowsAt3736))) (Checked.join (Checked.join (Checked.join rowsAt3768 rowsAt3800) (Checked.join rowsAt3832 rowsAt3864)) (Checked.join (Checked.join rowsAt3896 rowsAt3928) (Checked.join rowsAt3960 rowsAt3992)))))

end GaussianChains.Point22.Atlas.Tables
