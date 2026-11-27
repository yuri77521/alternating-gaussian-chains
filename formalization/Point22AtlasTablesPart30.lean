import Point22AtlasTablesPart29

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt1875 : Checked traceOK 1875 1879 :=
  Checked.of_segment (lo := 1875) (count := 4) (by decide +kernel)

private theorem bandsAt1879 : Checked traceOK 1879 1883 :=
  Checked.of_segment (lo := 1879) (count := 4) (by decide +kernel)

private theorem bandsAt1883 : Checked traceOK 1883 1887 :=
  Checked.of_segment (lo := 1883) (count := 4) (by decide +kernel)

private theorem bandsAt1887 : Checked traceOK 1887 1891 :=
  Checked.of_segment (lo := 1887) (count := 4) (by decide +kernel)

private theorem bandsAt1891 : Checked traceOK 1891 1895 :=
  Checked.of_segment (lo := 1891) (count := 4) (by decide +kernel)

private theorem bandsAt1895 : Checked traceOK 1895 1899 :=
  Checked.of_segment (lo := 1895) (count := 4) (by decide +kernel)

private theorem bandsAt1899 : Checked traceOK 1899 1903 :=
  Checked.of_segment (lo := 1899) (count := 4) (by decide +kernel)

private theorem bandsAt1903 : Checked traceOK 1903 1907 :=
  Checked.of_segment (lo := 1903) (count := 4) (by decide +kernel)

private theorem bandsAt1907 : Checked traceOK 1907 1911 :=
  Checked.of_segment (lo := 1907) (count := 4) (by decide +kernel)

private theorem bandsAt1911 : Checked traceOK 1911 1915 :=
  Checked.of_segment (lo := 1911) (count := 4) (by decide +kernel)

private theorem bandsAt1915 : Checked traceOK 1915 1919 :=
  Checked.of_segment (lo := 1915) (count := 4) (by decide +kernel)

private theorem bandsAt1919 : Checked traceOK 1919 1923 :=
  Checked.of_segment (lo := 1919) (count := 4) (by decide +kernel)

private theorem bandsAt1923 : Checked traceOK 1923 1927 :=
  Checked.of_segment (lo := 1923) (count := 4) (by decide +kernel)

private theorem bandsAt1927 : Checked traceOK 1927 1931 :=
  Checked.of_segment (lo := 1927) (count := 4) (by decide +kernel)

private theorem bandsAt1931 : Checked traceOK 1931 1935 :=
  Checked.of_segment (lo := 1931) (count := 4) (by decide +kernel)

private theorem bandsAt1935 : Checked traceOK 1935 1937 :=
  Checked.of_segment (lo := 1935) (count := 2) (by decide +kernel)

theorem bandsFrom1875 : Checked traceOK 1875 1937 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt1875 bandsAt1879) (Checked.join bandsAt1883 bandsAt1887)) (Checked.join (Checked.join bandsAt1891 bandsAt1895) (Checked.join bandsAt1899 bandsAt1903))) (Checked.join (Checked.join (Checked.join bandsAt1907 bandsAt1911) (Checked.join bandsAt1915 bandsAt1919)) (Checked.join (Checked.join bandsAt1923 bandsAt1927) (Checked.join bandsAt1931 bandsAt1935))))

private theorem rowsAt30000 : Checked rowOK 30000 30032 :=
  Checked.of_fused_segment (lo := 30000) (count := 32) (by decide +kernel)

private theorem rowsAt30032 : Checked rowOK 30032 30064 :=
  Checked.of_fused_segment (lo := 30032) (count := 32) (by decide +kernel)

private theorem rowsAt30064 : Checked rowOK 30064 30096 :=
  Checked.of_fused_segment (lo := 30064) (count := 32) (by decide +kernel)

private theorem rowsAt30096 : Checked rowOK 30096 30128 :=
  Checked.of_fused_segment (lo := 30096) (count := 32) (by decide +kernel)

private theorem rowsAt30128 : Checked rowOK 30128 30160 :=
  Checked.of_fused_segment (lo := 30128) (count := 32) (by decide +kernel)

private theorem rowsAt30160 : Checked rowOK 30160 30192 :=
  Checked.of_fused_segment (lo := 30160) (count := 32) (by decide +kernel)

private theorem rowsAt30192 : Checked rowOK 30192 30224 :=
  Checked.of_fused_segment (lo := 30192) (count := 32) (by decide +kernel)

private theorem rowsAt30224 : Checked rowOK 30224 30256 :=
  Checked.of_fused_segment (lo := 30224) (count := 32) (by decide +kernel)

private theorem rowsAt30256 : Checked rowOK 30256 30288 :=
  Checked.of_fused_segment (lo := 30256) (count := 32) (by decide +kernel)

private theorem rowsAt30288 : Checked rowOK 30288 30320 :=
  Checked.of_fused_segment (lo := 30288) (count := 32) (by decide +kernel)

private theorem rowsAt30320 : Checked rowOK 30320 30352 :=
  Checked.of_fused_segment (lo := 30320) (count := 32) (by decide +kernel)

private theorem rowsAt30352 : Checked rowOK 30352 30384 :=
  Checked.of_fused_segment (lo := 30352) (count := 32) (by decide +kernel)

private theorem rowsAt30384 : Checked rowOK 30384 30416 :=
  Checked.of_fused_segment (lo := 30384) (count := 32) (by decide +kernel)

private theorem rowsAt30416 : Checked rowOK 30416 30448 :=
  Checked.of_fused_segment (lo := 30416) (count := 32) (by decide +kernel)

private theorem rowsAt30448 : Checked rowOK 30448 30480 :=
  Checked.of_fused_segment (lo := 30448) (count := 32) (by decide +kernel)

private theorem rowsAt30480 : Checked rowOK 30480 30512 :=
  Checked.of_fused_segment (lo := 30480) (count := 32) (by decide +kernel)

private theorem rowsAt30512 : Checked rowOK 30512 30544 :=
  Checked.of_fused_segment (lo := 30512) (count := 32) (by decide +kernel)

private theorem rowsAt30544 : Checked rowOK 30544 30576 :=
  Checked.of_fused_segment (lo := 30544) (count := 32) (by decide +kernel)

private theorem rowsAt30576 : Checked rowOK 30576 30608 :=
  Checked.of_fused_segment (lo := 30576) (count := 32) (by decide +kernel)

private theorem rowsAt30608 : Checked rowOK 30608 30640 :=
  Checked.of_fused_segment (lo := 30608) (count := 32) (by decide +kernel)

private theorem rowsAt30640 : Checked rowOK 30640 30672 :=
  Checked.of_fused_segment (lo := 30640) (count := 32) (by decide +kernel)

private theorem rowsAt30672 : Checked rowOK 30672 30704 :=
  Checked.of_fused_segment (lo := 30672) (count := 32) (by decide +kernel)

private theorem rowsAt30704 : Checked rowOK 30704 30736 :=
  Checked.of_fused_segment (lo := 30704) (count := 32) (by decide +kernel)

private theorem rowsAt30736 : Checked rowOK 30736 30768 :=
  Checked.of_fused_segment (lo := 30736) (count := 32) (by decide +kernel)

private theorem rowsAt30768 : Checked rowOK 30768 30800 :=
  Checked.of_fused_segment (lo := 30768) (count := 32) (by decide +kernel)

private theorem rowsAt30800 : Checked rowOK 30800 30832 :=
  Checked.of_fused_segment (lo := 30800) (count := 32) (by decide +kernel)

private theorem rowsAt30832 : Checked rowOK 30832 30864 :=
  Checked.of_fused_segment (lo := 30832) (count := 32) (by decide +kernel)

private theorem rowsAt30864 : Checked rowOK 30864 30896 :=
  Checked.of_fused_segment (lo := 30864) (count := 32) (by decide +kernel)

private theorem rowsAt30896 : Checked rowOK 30896 30928 :=
  Checked.of_fused_segment (lo := 30896) (count := 32) (by decide +kernel)

private theorem rowsAt30928 : Checked rowOK 30928 30960 :=
  Checked.of_fused_segment (lo := 30928) (count := 32) (by decide +kernel)

private theorem rowsAt30960 : Checked rowOK 30960 30992 :=
  Checked.of_fused_segment (lo := 30960) (count := 32) (by decide +kernel)

private theorem rowsAt30992 : Checked rowOK 30992 31000 :=
  Checked.of_fused_segment (lo := 30992) (count := 8) (by decide +kernel)

theorem rowsFrom30000 : Checked rowOK 30000 31000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt30000 rowsAt30032) (Checked.join rowsAt30064 rowsAt30096)) (Checked.join (Checked.join rowsAt30128 rowsAt30160) (Checked.join rowsAt30192 rowsAt30224))) (Checked.join (Checked.join (Checked.join rowsAt30256 rowsAt30288) (Checked.join rowsAt30320 rowsAt30352)) (Checked.join (Checked.join rowsAt30384 rowsAt30416) (Checked.join rowsAt30448 rowsAt30480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt30512 rowsAt30544) (Checked.join rowsAt30576 rowsAt30608)) (Checked.join (Checked.join rowsAt30640 rowsAt30672) (Checked.join rowsAt30704 rowsAt30736))) (Checked.join (Checked.join (Checked.join rowsAt30768 rowsAt30800) (Checked.join rowsAt30832 rowsAt30864)) (Checked.join (Checked.join rowsAt30896 rowsAt30928) (Checked.join rowsAt30960 rowsAt30992)))))

end GaussianChains.Point22.Atlas.Tables
