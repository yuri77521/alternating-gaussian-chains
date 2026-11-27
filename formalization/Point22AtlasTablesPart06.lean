import Point22AtlasTablesPart05

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt375 : Checked traceOK 375 379 :=
  Checked.of_segment (lo := 375) (count := 4) (by decide +kernel)

private theorem bandsAt379 : Checked traceOK 379 383 :=
  Checked.of_segment (lo := 379) (count := 4) (by decide +kernel)

private theorem bandsAt383 : Checked traceOK 383 387 :=
  Checked.of_segment (lo := 383) (count := 4) (by decide +kernel)

private theorem bandsAt387 : Checked traceOK 387 391 :=
  Checked.of_segment (lo := 387) (count := 4) (by decide +kernel)

private theorem bandsAt391 : Checked traceOK 391 395 :=
  Checked.of_segment (lo := 391) (count := 4) (by decide +kernel)

private theorem bandsAt395 : Checked traceOK 395 399 :=
  Checked.of_segment (lo := 395) (count := 4) (by decide +kernel)

private theorem bandsAt399 : Checked traceOK 399 403 :=
  Checked.of_segment (lo := 399) (count := 4) (by decide +kernel)

private theorem bandsAt403 : Checked traceOK 403 407 :=
  Checked.of_segment (lo := 403) (count := 4) (by decide +kernel)

private theorem bandsAt407 : Checked traceOK 407 411 :=
  Checked.of_segment (lo := 407) (count := 4) (by decide +kernel)

private theorem bandsAt411 : Checked traceOK 411 415 :=
  Checked.of_segment (lo := 411) (count := 4) (by decide +kernel)

private theorem bandsAt415 : Checked traceOK 415 419 :=
  Checked.of_segment (lo := 415) (count := 4) (by decide +kernel)

private theorem bandsAt419 : Checked traceOK 419 423 :=
  Checked.of_segment (lo := 419) (count := 4) (by decide +kernel)

private theorem bandsAt423 : Checked traceOK 423 427 :=
  Checked.of_segment (lo := 423) (count := 4) (by decide +kernel)

private theorem bandsAt427 : Checked traceOK 427 431 :=
  Checked.of_segment (lo := 427) (count := 4) (by decide +kernel)

private theorem bandsAt431 : Checked traceOK 431 435 :=
  Checked.of_segment (lo := 431) (count := 4) (by decide +kernel)

private theorem bandsAt435 : Checked traceOK 435 437 :=
  Checked.of_segment (lo := 435) (count := 2) (by decide +kernel)

theorem bandsFrom375 : Checked traceOK 375 437 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt375 bandsAt379) (Checked.join bandsAt383 bandsAt387)) (Checked.join (Checked.join bandsAt391 bandsAt395) (Checked.join bandsAt399 bandsAt403))) (Checked.join (Checked.join (Checked.join bandsAt407 bandsAt411) (Checked.join bandsAt415 bandsAt419)) (Checked.join (Checked.join bandsAt423 bandsAt427) (Checked.join bandsAt431 bandsAt435))))

private theorem rowsAt6000 : Checked rowOK 6000 6032 :=
  Checked.of_segment (lo := 6000) (count := 32) (by decide +kernel)

private theorem rowsAt6032 : Checked rowOK 6032 6064 :=
  Checked.of_segment (lo := 6032) (count := 32) (by decide +kernel)

private theorem rowsAt6064 : Checked rowOK 6064 6096 :=
  Checked.of_segment (lo := 6064) (count := 32) (by decide +kernel)

private theorem rowsAt6096 : Checked rowOK 6096 6128 :=
  Checked.of_segment (lo := 6096) (count := 32) (by decide +kernel)

private theorem rowsAt6128 : Checked rowOK 6128 6160 :=
  Checked.of_segment (lo := 6128) (count := 32) (by decide +kernel)

private theorem rowsAt6160 : Checked rowOK 6160 6192 :=
  Checked.of_segment (lo := 6160) (count := 32) (by decide +kernel)

private theorem rowsAt6192 : Checked rowOK 6192 6224 :=
  Checked.of_segment (lo := 6192) (count := 32) (by decide +kernel)

private theorem rowsAt6224 : Checked rowOK 6224 6256 :=
  Checked.of_segment (lo := 6224) (count := 32) (by decide +kernel)

private theorem rowsAt6256 : Checked rowOK 6256 6288 :=
  Checked.of_segment (lo := 6256) (count := 32) (by decide +kernel)

private theorem rowsAt6288 : Checked rowOK 6288 6320 :=
  Checked.of_segment (lo := 6288) (count := 32) (by decide +kernel)

private theorem rowsAt6320 : Checked rowOK 6320 6352 :=
  Checked.of_segment (lo := 6320) (count := 32) (by decide +kernel)

private theorem rowsAt6352 : Checked rowOK 6352 6384 :=
  Checked.of_segment (lo := 6352) (count := 32) (by decide +kernel)

private theorem rowsAt6384 : Checked rowOK 6384 6416 :=
  Checked.of_segment (lo := 6384) (count := 32) (by decide +kernel)

private theorem rowsAt6416 : Checked rowOK 6416 6448 :=
  Checked.of_segment (lo := 6416) (count := 32) (by decide +kernel)

private theorem rowsAt6448 : Checked rowOK 6448 6480 :=
  Checked.of_segment (lo := 6448) (count := 32) (by decide +kernel)

private theorem rowsAt6480 : Checked rowOK 6480 6512 :=
  Checked.of_segment (lo := 6480) (count := 32) (by decide +kernel)

private theorem rowsAt6512 : Checked rowOK 6512 6544 :=
  Checked.of_segment (lo := 6512) (count := 32) (by decide +kernel)

private theorem rowsAt6544 : Checked rowOK 6544 6576 :=
  Checked.of_segment (lo := 6544) (count := 32) (by decide +kernel)

private theorem rowsAt6576 : Checked rowOK 6576 6608 :=
  Checked.of_segment (lo := 6576) (count := 32) (by decide +kernel)

private theorem rowsAt6608 : Checked rowOK 6608 6640 :=
  Checked.of_segment (lo := 6608) (count := 32) (by decide +kernel)

private theorem rowsAt6640 : Checked rowOK 6640 6672 :=
  Checked.of_segment (lo := 6640) (count := 32) (by decide +kernel)

private theorem rowsAt6672 : Checked rowOK 6672 6704 :=
  Checked.of_segment (lo := 6672) (count := 32) (by decide +kernel)

private theorem rowsAt6704 : Checked rowOK 6704 6736 :=
  Checked.of_segment (lo := 6704) (count := 32) (by decide +kernel)

private theorem rowsAt6736 : Checked rowOK 6736 6768 :=
  Checked.of_segment (lo := 6736) (count := 32) (by decide +kernel)

private theorem rowsAt6768 : Checked rowOK 6768 6800 :=
  Checked.of_segment (lo := 6768) (count := 32) (by decide +kernel)

private theorem rowsAt6800 : Checked rowOK 6800 6832 :=
  Checked.of_segment (lo := 6800) (count := 32) (by decide +kernel)

private theorem rowsAt6832 : Checked rowOK 6832 6864 :=
  Checked.of_segment (lo := 6832) (count := 32) (by decide +kernel)

private theorem rowsAt6864 : Checked rowOK 6864 6896 :=
  Checked.of_segment (lo := 6864) (count := 32) (by decide +kernel)

private theorem rowsAt6896 : Checked rowOK 6896 6928 :=
  Checked.of_segment (lo := 6896) (count := 32) (by decide +kernel)

private theorem rowsAt6928 : Checked rowOK 6928 6960 :=
  Checked.of_segment (lo := 6928) (count := 32) (by decide +kernel)

private theorem rowsAt6960 : Checked rowOK 6960 6992 :=
  Checked.of_segment (lo := 6960) (count := 32) (by decide +kernel)

private theorem rowsAt6992 : Checked rowOK 6992 7000 :=
  Checked.of_segment (lo := 6992) (count := 8) (by decide +kernel)

theorem rowsFrom6000 : Checked rowOK 6000 7000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt6000 rowsAt6032) (Checked.join rowsAt6064 rowsAt6096)) (Checked.join (Checked.join rowsAt6128 rowsAt6160) (Checked.join rowsAt6192 rowsAt6224))) (Checked.join (Checked.join (Checked.join rowsAt6256 rowsAt6288) (Checked.join rowsAt6320 rowsAt6352)) (Checked.join (Checked.join rowsAt6384 rowsAt6416) (Checked.join rowsAt6448 rowsAt6480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt6512 rowsAt6544) (Checked.join rowsAt6576 rowsAt6608)) (Checked.join (Checked.join rowsAt6640 rowsAt6672) (Checked.join rowsAt6704 rowsAt6736))) (Checked.join (Checked.join (Checked.join rowsAt6768 rowsAt6800) (Checked.join rowsAt6832 rowsAt6864)) (Checked.join (Checked.join rowsAt6896 rowsAt6928) (Checked.join rowsAt6960 rowsAt6992)))))

end GaussianChains.Point22.Atlas.Tables
