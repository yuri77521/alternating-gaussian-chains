import Point22AtlasTablesPart04

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt312 : Checked traceOK 312 316 :=
  Checked.of_segment (lo := 312) (count := 4) (by decide +kernel)

private theorem bandsAt316 : Checked traceOK 316 320 :=
  Checked.of_segment (lo := 316) (count := 4) (by decide +kernel)

private theorem bandsAt320 : Checked traceOK 320 324 :=
  Checked.of_segment (lo := 320) (count := 4) (by decide +kernel)

private theorem bandsAt324 : Checked traceOK 324 328 :=
  Checked.of_segment (lo := 324) (count := 4) (by decide +kernel)

private theorem bandsAt328 : Checked traceOK 328 332 :=
  Checked.of_segment (lo := 328) (count := 4) (by decide +kernel)

private theorem bandsAt332 : Checked traceOK 332 336 :=
  Checked.of_segment (lo := 332) (count := 4) (by decide +kernel)

private theorem bandsAt336 : Checked traceOK 336 340 :=
  Checked.of_segment (lo := 336) (count := 4) (by decide +kernel)

private theorem bandsAt340 : Checked traceOK 340 344 :=
  Checked.of_segment (lo := 340) (count := 4) (by decide +kernel)

private theorem bandsAt344 : Checked traceOK 344 348 :=
  Checked.of_segment (lo := 344) (count := 4) (by decide +kernel)

private theorem bandsAt348 : Checked traceOK 348 352 :=
  Checked.of_segment (lo := 348) (count := 4) (by decide +kernel)

private theorem bandsAt352 : Checked traceOK 352 356 :=
  Checked.of_segment (lo := 352) (count := 4) (by decide +kernel)

private theorem bandsAt356 : Checked traceOK 356 360 :=
  Checked.of_segment (lo := 356) (count := 4) (by decide +kernel)

private theorem bandsAt360 : Checked traceOK 360 364 :=
  Checked.of_segment (lo := 360) (count := 4) (by decide +kernel)

private theorem bandsAt364 : Checked traceOK 364 368 :=
  Checked.of_segment (lo := 364) (count := 4) (by decide +kernel)

private theorem bandsAt368 : Checked traceOK 368 372 :=
  Checked.of_segment (lo := 368) (count := 4) (by decide +kernel)

private theorem bandsAt372 : Checked traceOK 372 375 :=
  Checked.of_segment (lo := 372) (count := 3) (by decide +kernel)

theorem bandsFrom312 : Checked traceOK 312 375 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt312 bandsAt316) (Checked.join bandsAt320 bandsAt324)) (Checked.join (Checked.join bandsAt328 bandsAt332) (Checked.join bandsAt336 bandsAt340))) (Checked.join (Checked.join (Checked.join bandsAt344 bandsAt348) (Checked.join bandsAt352 bandsAt356)) (Checked.join (Checked.join bandsAt360 bandsAt364) (Checked.join bandsAt368 bandsAt372))))

private theorem rowsAt5000 : Checked rowOK 5000 5032 :=
  Checked.of_segment (lo := 5000) (count := 32) (by decide +kernel)

private theorem rowsAt5032 : Checked rowOK 5032 5064 :=
  Checked.of_segment (lo := 5032) (count := 32) (by decide +kernel)

private theorem rowsAt5064 : Checked rowOK 5064 5096 :=
  Checked.of_segment (lo := 5064) (count := 32) (by decide +kernel)

private theorem rowsAt5096 : Checked rowOK 5096 5128 :=
  Checked.of_segment (lo := 5096) (count := 32) (by decide +kernel)

private theorem rowsAt5128 : Checked rowOK 5128 5160 :=
  Checked.of_segment (lo := 5128) (count := 32) (by decide +kernel)

private theorem rowsAt5160 : Checked rowOK 5160 5192 :=
  Checked.of_segment (lo := 5160) (count := 32) (by decide +kernel)

private theorem rowsAt5192 : Checked rowOK 5192 5224 :=
  Checked.of_segment (lo := 5192) (count := 32) (by decide +kernel)

private theorem rowsAt5224 : Checked rowOK 5224 5256 :=
  Checked.of_segment (lo := 5224) (count := 32) (by decide +kernel)

private theorem rowsAt5256 : Checked rowOK 5256 5288 :=
  Checked.of_segment (lo := 5256) (count := 32) (by decide +kernel)

private theorem rowsAt5288 : Checked rowOK 5288 5320 :=
  Checked.of_segment (lo := 5288) (count := 32) (by decide +kernel)

private theorem rowsAt5320 : Checked rowOK 5320 5352 :=
  Checked.of_segment (lo := 5320) (count := 32) (by decide +kernel)

private theorem rowsAt5352 : Checked rowOK 5352 5384 :=
  Checked.of_segment (lo := 5352) (count := 32) (by decide +kernel)

private theorem rowsAt5384 : Checked rowOK 5384 5416 :=
  Checked.of_segment (lo := 5384) (count := 32) (by decide +kernel)

private theorem rowsAt5416 : Checked rowOK 5416 5448 :=
  Checked.of_segment (lo := 5416) (count := 32) (by decide +kernel)

private theorem rowsAt5448 : Checked rowOK 5448 5480 :=
  Checked.of_segment (lo := 5448) (count := 32) (by decide +kernel)

private theorem rowsAt5480 : Checked rowOK 5480 5512 :=
  Checked.of_segment (lo := 5480) (count := 32) (by decide +kernel)

private theorem rowsAt5512 : Checked rowOK 5512 5544 :=
  Checked.of_segment (lo := 5512) (count := 32) (by decide +kernel)

private theorem rowsAt5544 : Checked rowOK 5544 5576 :=
  Checked.of_segment (lo := 5544) (count := 32) (by decide +kernel)

private theorem rowsAt5576 : Checked rowOK 5576 5608 :=
  Checked.of_segment (lo := 5576) (count := 32) (by decide +kernel)

private theorem rowsAt5608 : Checked rowOK 5608 5640 :=
  Checked.of_segment (lo := 5608) (count := 32) (by decide +kernel)

private theorem rowsAt5640 : Checked rowOK 5640 5672 :=
  Checked.of_segment (lo := 5640) (count := 32) (by decide +kernel)

private theorem rowsAt5672 : Checked rowOK 5672 5704 :=
  Checked.of_segment (lo := 5672) (count := 32) (by decide +kernel)

private theorem rowsAt5704 : Checked rowOK 5704 5736 :=
  Checked.of_segment (lo := 5704) (count := 32) (by decide +kernel)

private theorem rowsAt5736 : Checked rowOK 5736 5768 :=
  Checked.of_segment (lo := 5736) (count := 32) (by decide +kernel)

private theorem rowsAt5768 : Checked rowOK 5768 5800 :=
  Checked.of_segment (lo := 5768) (count := 32) (by decide +kernel)

private theorem rowsAt5800 : Checked rowOK 5800 5832 :=
  Checked.of_segment (lo := 5800) (count := 32) (by decide +kernel)

private theorem rowsAt5832 : Checked rowOK 5832 5864 :=
  Checked.of_segment (lo := 5832) (count := 32) (by decide +kernel)

private theorem rowsAt5864 : Checked rowOK 5864 5896 :=
  Checked.of_segment (lo := 5864) (count := 32) (by decide +kernel)

private theorem rowsAt5896 : Checked rowOK 5896 5928 :=
  Checked.of_segment (lo := 5896) (count := 32) (by decide +kernel)

private theorem rowsAt5928 : Checked rowOK 5928 5960 :=
  Checked.of_segment (lo := 5928) (count := 32) (by decide +kernel)

private theorem rowsAt5960 : Checked rowOK 5960 5992 :=
  Checked.of_segment (lo := 5960) (count := 32) (by decide +kernel)

private theorem rowsAt5992 : Checked rowOK 5992 6000 :=
  Checked.of_segment (lo := 5992) (count := 8) (by decide +kernel)

theorem rowsFrom5000 : Checked rowOK 5000 6000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt5000 rowsAt5032) (Checked.join rowsAt5064 rowsAt5096)) (Checked.join (Checked.join rowsAt5128 rowsAt5160) (Checked.join rowsAt5192 rowsAt5224))) (Checked.join (Checked.join (Checked.join rowsAt5256 rowsAt5288) (Checked.join rowsAt5320 rowsAt5352)) (Checked.join (Checked.join rowsAt5384 rowsAt5416) (Checked.join rowsAt5448 rowsAt5480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt5512 rowsAt5544) (Checked.join rowsAt5576 rowsAt5608)) (Checked.join (Checked.join rowsAt5640 rowsAt5672) (Checked.join rowsAt5704 rowsAt5736))) (Checked.join (Checked.join (Checked.join rowsAt5768 rowsAt5800) (Checked.join rowsAt5832 rowsAt5864)) (Checked.join (Checked.join rowsAt5896 rowsAt5928) (Checked.join rowsAt5960 rowsAt5992)))))

end GaussianChains.Point22.Atlas.Tables
