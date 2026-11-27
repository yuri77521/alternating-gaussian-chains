import Point22AtlasTablesPart27

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt1750 : Checked traceOK 1750 1754 :=
  Checked.of_segment (lo := 1750) (count := 4) (by decide +kernel)

private theorem bandsAt1754 : Checked traceOK 1754 1758 :=
  Checked.of_segment (lo := 1754) (count := 4) (by decide +kernel)

private theorem bandsAt1758 : Checked traceOK 1758 1762 :=
  Checked.of_segment (lo := 1758) (count := 4) (by decide +kernel)

private theorem bandsAt1762 : Checked traceOK 1762 1766 :=
  Checked.of_segment (lo := 1762) (count := 4) (by decide +kernel)

private theorem bandsAt1766 : Checked traceOK 1766 1770 :=
  Checked.of_segment (lo := 1766) (count := 4) (by decide +kernel)

private theorem bandsAt1770 : Checked traceOK 1770 1774 :=
  Checked.of_segment (lo := 1770) (count := 4) (by decide +kernel)

private theorem bandsAt1774 : Checked traceOK 1774 1778 :=
  Checked.of_segment (lo := 1774) (count := 4) (by decide +kernel)

private theorem bandsAt1778 : Checked traceOK 1778 1782 :=
  Checked.of_segment (lo := 1778) (count := 4) (by decide +kernel)

private theorem bandsAt1782 : Checked traceOK 1782 1786 :=
  Checked.of_segment (lo := 1782) (count := 4) (by decide +kernel)

private theorem bandsAt1786 : Checked traceOK 1786 1790 :=
  Checked.of_segment (lo := 1786) (count := 4) (by decide +kernel)

private theorem bandsAt1790 : Checked traceOK 1790 1794 :=
  Checked.of_segment (lo := 1790) (count := 4) (by decide +kernel)

private theorem bandsAt1794 : Checked traceOK 1794 1798 :=
  Checked.of_segment (lo := 1794) (count := 4) (by decide +kernel)

private theorem bandsAt1798 : Checked traceOK 1798 1802 :=
  Checked.of_segment (lo := 1798) (count := 4) (by decide +kernel)

private theorem bandsAt1802 : Checked traceOK 1802 1806 :=
  Checked.of_segment (lo := 1802) (count := 4) (by decide +kernel)

private theorem bandsAt1806 : Checked traceOK 1806 1810 :=
  Checked.of_segment (lo := 1806) (count := 4) (by decide +kernel)

private theorem bandsAt1810 : Checked traceOK 1810 1812 :=
  Checked.of_segment (lo := 1810) (count := 2) (by decide +kernel)

theorem bandsFrom1750 : Checked traceOK 1750 1812 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt1750 bandsAt1754) (Checked.join bandsAt1758 bandsAt1762)) (Checked.join (Checked.join bandsAt1766 bandsAt1770) (Checked.join bandsAt1774 bandsAt1778))) (Checked.join (Checked.join (Checked.join bandsAt1782 bandsAt1786) (Checked.join bandsAt1790 bandsAt1794)) (Checked.join (Checked.join bandsAt1798 bandsAt1802) (Checked.join bandsAt1806 bandsAt1810))))

private theorem rowsAt28000 : Checked rowOK 28000 28032 :=
  Checked.of_fused_segment (lo := 28000) (count := 32) (by decide +kernel)

private theorem rowsAt28032 : Checked rowOK 28032 28064 :=
  Checked.of_fused_segment (lo := 28032) (count := 32) (by decide +kernel)

private theorem rowsAt28064 : Checked rowOK 28064 28096 :=
  Checked.of_fused_segment (lo := 28064) (count := 32) (by decide +kernel)

private theorem rowsAt28096 : Checked rowOK 28096 28128 :=
  Checked.of_fused_segment (lo := 28096) (count := 32) (by decide +kernel)

private theorem rowsAt28128 : Checked rowOK 28128 28160 :=
  Checked.of_fused_segment (lo := 28128) (count := 32) (by decide +kernel)

private theorem rowsAt28160 : Checked rowOK 28160 28192 :=
  Checked.of_fused_segment (lo := 28160) (count := 32) (by decide +kernel)

private theorem rowsAt28192 : Checked rowOK 28192 28224 :=
  Checked.of_fused_segment (lo := 28192) (count := 32) (by decide +kernel)

private theorem rowsAt28224 : Checked rowOK 28224 28256 :=
  Checked.of_fused_segment (lo := 28224) (count := 32) (by decide +kernel)

private theorem rowsAt28256 : Checked rowOK 28256 28288 :=
  Checked.of_fused_segment (lo := 28256) (count := 32) (by decide +kernel)

private theorem rowsAt28288 : Checked rowOK 28288 28320 :=
  Checked.of_fused_segment (lo := 28288) (count := 32) (by decide +kernel)

private theorem rowsAt28320 : Checked rowOK 28320 28352 :=
  Checked.of_fused_segment (lo := 28320) (count := 32) (by decide +kernel)

private theorem rowsAt28352 : Checked rowOK 28352 28384 :=
  Checked.of_fused_segment (lo := 28352) (count := 32) (by decide +kernel)

private theorem rowsAt28384 : Checked rowOK 28384 28416 :=
  Checked.of_fused_segment (lo := 28384) (count := 32) (by decide +kernel)

private theorem rowsAt28416 : Checked rowOK 28416 28448 :=
  Checked.of_fused_segment (lo := 28416) (count := 32) (by decide +kernel)

private theorem rowsAt28448 : Checked rowOK 28448 28480 :=
  Checked.of_fused_segment (lo := 28448) (count := 32) (by decide +kernel)

private theorem rowsAt28480 : Checked rowOK 28480 28512 :=
  Checked.of_fused_segment (lo := 28480) (count := 32) (by decide +kernel)

private theorem rowsAt28512 : Checked rowOK 28512 28544 :=
  Checked.of_fused_segment (lo := 28512) (count := 32) (by decide +kernel)

private theorem rowsAt28544 : Checked rowOK 28544 28576 :=
  Checked.of_fused_segment (lo := 28544) (count := 32) (by decide +kernel)

private theorem rowsAt28576 : Checked rowOK 28576 28608 :=
  Checked.of_fused_segment (lo := 28576) (count := 32) (by decide +kernel)

private theorem rowsAt28608 : Checked rowOK 28608 28640 :=
  Checked.of_fused_segment (lo := 28608) (count := 32) (by decide +kernel)

private theorem rowsAt28640 : Checked rowOK 28640 28672 :=
  Checked.of_fused_segment (lo := 28640) (count := 32) (by decide +kernel)

private theorem rowsAt28672 : Checked rowOK 28672 28704 :=
  Checked.of_fused_segment (lo := 28672) (count := 32) (by decide +kernel)

private theorem rowsAt28704 : Checked rowOK 28704 28736 :=
  Checked.of_fused_segment (lo := 28704) (count := 32) (by decide +kernel)

private theorem rowsAt28736 : Checked rowOK 28736 28768 :=
  Checked.of_fused_segment (lo := 28736) (count := 32) (by decide +kernel)

private theorem rowsAt28768 : Checked rowOK 28768 28800 :=
  Checked.of_fused_segment (lo := 28768) (count := 32) (by decide +kernel)

private theorem rowsAt28800 : Checked rowOK 28800 28832 :=
  Checked.of_fused_segment (lo := 28800) (count := 32) (by decide +kernel)

private theorem rowsAt28832 : Checked rowOK 28832 28864 :=
  Checked.of_fused_segment (lo := 28832) (count := 32) (by decide +kernel)

private theorem rowsAt28864 : Checked rowOK 28864 28896 :=
  Checked.of_fused_segment (lo := 28864) (count := 32) (by decide +kernel)

private theorem rowsAt28896 : Checked rowOK 28896 28928 :=
  Checked.of_fused_segment (lo := 28896) (count := 32) (by decide +kernel)

private theorem rowsAt28928 : Checked rowOK 28928 28960 :=
  Checked.of_fused_segment (lo := 28928) (count := 32) (by decide +kernel)

private theorem rowsAt28960 : Checked rowOK 28960 28992 :=
  Checked.of_fused_segment (lo := 28960) (count := 32) (by decide +kernel)

private theorem rowsAt28992 : Checked rowOK 28992 29000 :=
  Checked.of_fused_segment (lo := 28992) (count := 8) (by decide +kernel)

theorem rowsFrom28000 : Checked rowOK 28000 29000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt28000 rowsAt28032) (Checked.join rowsAt28064 rowsAt28096)) (Checked.join (Checked.join rowsAt28128 rowsAt28160) (Checked.join rowsAt28192 rowsAt28224))) (Checked.join (Checked.join (Checked.join rowsAt28256 rowsAt28288) (Checked.join rowsAt28320 rowsAt28352)) (Checked.join (Checked.join rowsAt28384 rowsAt28416) (Checked.join rowsAt28448 rowsAt28480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt28512 rowsAt28544) (Checked.join rowsAt28576 rowsAt28608)) (Checked.join (Checked.join rowsAt28640 rowsAt28672) (Checked.join rowsAt28704 rowsAt28736))) (Checked.join (Checked.join (Checked.join rowsAt28768 rowsAt28800) (Checked.join rowsAt28832 rowsAt28864)) (Checked.join (Checked.join rowsAt28896 rowsAt28928) (Checked.join rowsAt28960 rowsAt28992)))))

end GaussianChains.Point22.Atlas.Tables
