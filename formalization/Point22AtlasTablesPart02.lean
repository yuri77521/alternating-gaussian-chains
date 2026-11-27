import Point22AtlasTablesPart01

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt125 : Checked traceOK 125 129 :=
  Checked.of_segment (lo := 125) (count := 4) (by decide +kernel)

private theorem bandsAt129 : Checked traceOK 129 133 :=
  Checked.of_segment (lo := 129) (count := 4) (by decide +kernel)

private theorem bandsAt133 : Checked traceOK 133 137 :=
  Checked.of_segment (lo := 133) (count := 4) (by decide +kernel)

private theorem bandsAt137 : Checked traceOK 137 141 :=
  Checked.of_segment (lo := 137) (count := 4) (by decide +kernel)

private theorem bandsAt141 : Checked traceOK 141 145 :=
  Checked.of_segment (lo := 141) (count := 4) (by decide +kernel)

private theorem bandsAt145 : Checked traceOK 145 149 :=
  Checked.of_segment (lo := 145) (count := 4) (by decide +kernel)

private theorem bandsAt149 : Checked traceOK 149 153 :=
  Checked.of_segment (lo := 149) (count := 4) (by decide +kernel)

private theorem bandsAt153 : Checked traceOK 153 157 :=
  Checked.of_segment (lo := 153) (count := 4) (by decide +kernel)

private theorem bandsAt157 : Checked traceOK 157 161 :=
  Checked.of_segment (lo := 157) (count := 4) (by decide +kernel)

private theorem bandsAt161 : Checked traceOK 161 165 :=
  Checked.of_segment (lo := 161) (count := 4) (by decide +kernel)

private theorem bandsAt165 : Checked traceOK 165 169 :=
  Checked.of_segment (lo := 165) (count := 4) (by decide +kernel)

private theorem bandsAt169 : Checked traceOK 169 173 :=
  Checked.of_segment (lo := 169) (count := 4) (by decide +kernel)

private theorem bandsAt173 : Checked traceOK 173 177 :=
  Checked.of_segment (lo := 173) (count := 4) (by decide +kernel)

private theorem bandsAt177 : Checked traceOK 177 181 :=
  Checked.of_segment (lo := 177) (count := 4) (by decide +kernel)

private theorem bandsAt181 : Checked traceOK 181 185 :=
  Checked.of_segment (lo := 181) (count := 4) (by decide +kernel)

private theorem bandsAt185 : Checked traceOK 185 187 :=
  Checked.of_segment (lo := 185) (count := 2) (by decide +kernel)

theorem bandsFrom125 : Checked traceOK 125 187 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt125 bandsAt129) (Checked.join bandsAt133 bandsAt137)) (Checked.join (Checked.join bandsAt141 bandsAt145) (Checked.join bandsAt149 bandsAt153))) (Checked.join (Checked.join (Checked.join bandsAt157 bandsAt161) (Checked.join bandsAt165 bandsAt169)) (Checked.join (Checked.join bandsAt173 bandsAt177) (Checked.join bandsAt181 bandsAt185))))

private theorem rowsAt2000 : Checked rowOK 2000 2032 :=
  Checked.of_segment (lo := 2000) (count := 32) (by decide +kernel)

private theorem rowsAt2032 : Checked rowOK 2032 2064 :=
  Checked.of_segment (lo := 2032) (count := 32) (by decide +kernel)

private theorem rowsAt2064 : Checked rowOK 2064 2096 :=
  Checked.of_segment (lo := 2064) (count := 32) (by decide +kernel)

private theorem rowsAt2096 : Checked rowOK 2096 2128 :=
  Checked.of_segment (lo := 2096) (count := 32) (by decide +kernel)

private theorem rowsAt2128 : Checked rowOK 2128 2160 :=
  Checked.of_segment (lo := 2128) (count := 32) (by decide +kernel)

private theorem rowsAt2160 : Checked rowOK 2160 2192 :=
  Checked.of_segment (lo := 2160) (count := 32) (by decide +kernel)

private theorem rowsAt2192 : Checked rowOK 2192 2224 :=
  Checked.of_segment (lo := 2192) (count := 32) (by decide +kernel)

private theorem rowsAt2224 : Checked rowOK 2224 2256 :=
  Checked.of_segment (lo := 2224) (count := 32) (by decide +kernel)

private theorem rowsAt2256 : Checked rowOK 2256 2288 :=
  Checked.of_segment (lo := 2256) (count := 32) (by decide +kernel)

private theorem rowsAt2288 : Checked rowOK 2288 2320 :=
  Checked.of_segment (lo := 2288) (count := 32) (by decide +kernel)

private theorem rowsAt2320 : Checked rowOK 2320 2352 :=
  Checked.of_segment (lo := 2320) (count := 32) (by decide +kernel)

private theorem rowsAt2352 : Checked rowOK 2352 2384 :=
  Checked.of_segment (lo := 2352) (count := 32) (by decide +kernel)

private theorem rowsAt2384 : Checked rowOK 2384 2416 :=
  Checked.of_segment (lo := 2384) (count := 32) (by decide +kernel)

private theorem rowsAt2416 : Checked rowOK 2416 2448 :=
  Checked.of_segment (lo := 2416) (count := 32) (by decide +kernel)

private theorem rowsAt2448 : Checked rowOK 2448 2480 :=
  Checked.of_segment (lo := 2448) (count := 32) (by decide +kernel)

private theorem rowsAt2480 : Checked rowOK 2480 2512 :=
  Checked.of_segment (lo := 2480) (count := 32) (by decide +kernel)

private theorem rowsAt2512 : Checked rowOK 2512 2544 :=
  Checked.of_segment (lo := 2512) (count := 32) (by decide +kernel)

private theorem rowsAt2544 : Checked rowOK 2544 2576 :=
  Checked.of_segment (lo := 2544) (count := 32) (by decide +kernel)

private theorem rowsAt2576 : Checked rowOK 2576 2608 :=
  Checked.of_segment (lo := 2576) (count := 32) (by decide +kernel)

private theorem rowsAt2608 : Checked rowOK 2608 2640 :=
  Checked.of_segment (lo := 2608) (count := 32) (by decide +kernel)

private theorem rowsAt2640 : Checked rowOK 2640 2672 :=
  Checked.of_segment (lo := 2640) (count := 32) (by decide +kernel)

private theorem rowsAt2672 : Checked rowOK 2672 2704 :=
  Checked.of_segment (lo := 2672) (count := 32) (by decide +kernel)

private theorem rowsAt2704 : Checked rowOK 2704 2736 :=
  Checked.of_segment (lo := 2704) (count := 32) (by decide +kernel)

private theorem rowsAt2736 : Checked rowOK 2736 2768 :=
  Checked.of_segment (lo := 2736) (count := 32) (by decide +kernel)

private theorem rowsAt2768 : Checked rowOK 2768 2800 :=
  Checked.of_segment (lo := 2768) (count := 32) (by decide +kernel)

private theorem rowsAt2800 : Checked rowOK 2800 2832 :=
  Checked.of_segment (lo := 2800) (count := 32) (by decide +kernel)

private theorem rowsAt2832 : Checked rowOK 2832 2864 :=
  Checked.of_segment (lo := 2832) (count := 32) (by decide +kernel)

private theorem rowsAt2864 : Checked rowOK 2864 2896 :=
  Checked.of_segment (lo := 2864) (count := 32) (by decide +kernel)

private theorem rowsAt2896 : Checked rowOK 2896 2928 :=
  Checked.of_segment (lo := 2896) (count := 32) (by decide +kernel)

private theorem rowsAt2928 : Checked rowOK 2928 2960 :=
  Checked.of_segment (lo := 2928) (count := 32) (by decide +kernel)

private theorem rowsAt2960 : Checked rowOK 2960 2992 :=
  Checked.of_segment (lo := 2960) (count := 32) (by decide +kernel)

private theorem rowsAt2992 : Checked rowOK 2992 3000 :=
  Checked.of_segment (lo := 2992) (count := 8) (by decide +kernel)

theorem rowsFrom2000 : Checked rowOK 2000 3000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt2000 rowsAt2032) (Checked.join rowsAt2064 rowsAt2096)) (Checked.join (Checked.join rowsAt2128 rowsAt2160) (Checked.join rowsAt2192 rowsAt2224))) (Checked.join (Checked.join (Checked.join rowsAt2256 rowsAt2288) (Checked.join rowsAt2320 rowsAt2352)) (Checked.join (Checked.join rowsAt2384 rowsAt2416) (Checked.join rowsAt2448 rowsAt2480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt2512 rowsAt2544) (Checked.join rowsAt2576 rowsAt2608)) (Checked.join (Checked.join rowsAt2640 rowsAt2672) (Checked.join rowsAt2704 rowsAt2736))) (Checked.join (Checked.join (Checked.join rowsAt2768 rowsAt2800) (Checked.join rowsAt2832 rowsAt2864)) (Checked.join (Checked.join rowsAt2896 rowsAt2928) (Checked.join rowsAt2960 rowsAt2992)))))

end GaussianChains.Point22.Atlas.Tables
