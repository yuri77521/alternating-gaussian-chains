import Point22AtlasTablesPart25

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt1625 : Checked traceOK 1625 1629 :=
  Checked.of_segment (lo := 1625) (count := 4) (by decide +kernel)

private theorem bandsAt1629 : Checked traceOK 1629 1633 :=
  Checked.of_segment (lo := 1629) (count := 4) (by decide +kernel)

private theorem bandsAt1633 : Checked traceOK 1633 1637 :=
  Checked.of_segment (lo := 1633) (count := 4) (by decide +kernel)

private theorem bandsAt1637 : Checked traceOK 1637 1641 :=
  Checked.of_segment (lo := 1637) (count := 4) (by decide +kernel)

private theorem bandsAt1641 : Checked traceOK 1641 1645 :=
  Checked.of_segment (lo := 1641) (count := 4) (by decide +kernel)

private theorem bandsAt1645 : Checked traceOK 1645 1649 :=
  Checked.of_segment (lo := 1645) (count := 4) (by decide +kernel)

private theorem bandsAt1649 : Checked traceOK 1649 1653 :=
  Checked.of_segment (lo := 1649) (count := 4) (by decide +kernel)

private theorem bandsAt1653 : Checked traceOK 1653 1657 :=
  Checked.of_segment (lo := 1653) (count := 4) (by decide +kernel)

private theorem bandsAt1657 : Checked traceOK 1657 1661 :=
  Checked.of_segment (lo := 1657) (count := 4) (by decide +kernel)

private theorem bandsAt1661 : Checked traceOK 1661 1665 :=
  Checked.of_segment (lo := 1661) (count := 4) (by decide +kernel)

private theorem bandsAt1665 : Checked traceOK 1665 1669 :=
  Checked.of_segment (lo := 1665) (count := 4) (by decide +kernel)

private theorem bandsAt1669 : Checked traceOK 1669 1673 :=
  Checked.of_segment (lo := 1669) (count := 4) (by decide +kernel)

private theorem bandsAt1673 : Checked traceOK 1673 1677 :=
  Checked.of_segment (lo := 1673) (count := 4) (by decide +kernel)

private theorem bandsAt1677 : Checked traceOK 1677 1681 :=
  Checked.of_segment (lo := 1677) (count := 4) (by decide +kernel)

private theorem bandsAt1681 : Checked traceOK 1681 1685 :=
  Checked.of_segment (lo := 1681) (count := 4) (by decide +kernel)

private theorem bandsAt1685 : Checked traceOK 1685 1687 :=
  Checked.of_segment (lo := 1685) (count := 2) (by decide +kernel)

theorem bandsFrom1625 : Checked traceOK 1625 1687 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt1625 bandsAt1629) (Checked.join bandsAt1633 bandsAt1637)) (Checked.join (Checked.join bandsAt1641 bandsAt1645) (Checked.join bandsAt1649 bandsAt1653))) (Checked.join (Checked.join (Checked.join bandsAt1657 bandsAt1661) (Checked.join bandsAt1665 bandsAt1669)) (Checked.join (Checked.join bandsAt1673 bandsAt1677) (Checked.join bandsAt1681 bandsAt1685))))

private theorem rowsAt26000 : Checked rowOK 26000 26032 :=
  Checked.of_fused_segment (lo := 26000) (count := 32) (by decide +kernel)

private theorem rowsAt26032 : Checked rowOK 26032 26064 :=
  Checked.of_fused_segment (lo := 26032) (count := 32) (by decide +kernel)

private theorem rowsAt26064 : Checked rowOK 26064 26096 :=
  Checked.of_fused_segment (lo := 26064) (count := 32) (by decide +kernel)

private theorem rowsAt26096 : Checked rowOK 26096 26128 :=
  Checked.of_fused_segment (lo := 26096) (count := 32) (by decide +kernel)

private theorem rowsAt26128 : Checked rowOK 26128 26160 :=
  Checked.of_fused_segment (lo := 26128) (count := 32) (by decide +kernel)

private theorem rowsAt26160 : Checked rowOK 26160 26192 :=
  Checked.of_fused_segment (lo := 26160) (count := 32) (by decide +kernel)

private theorem rowsAt26192 : Checked rowOK 26192 26224 :=
  Checked.of_fused_segment (lo := 26192) (count := 32) (by decide +kernel)

private theorem rowsAt26224 : Checked rowOK 26224 26256 :=
  Checked.of_fused_segment (lo := 26224) (count := 32) (by decide +kernel)

private theorem rowsAt26256 : Checked rowOK 26256 26288 :=
  Checked.of_fused_segment (lo := 26256) (count := 32) (by decide +kernel)

private theorem rowsAt26288 : Checked rowOK 26288 26320 :=
  Checked.of_fused_segment (lo := 26288) (count := 32) (by decide +kernel)

private theorem rowsAt26320 : Checked rowOK 26320 26352 :=
  Checked.of_fused_segment (lo := 26320) (count := 32) (by decide +kernel)

private theorem rowsAt26352 : Checked rowOK 26352 26384 :=
  Checked.of_fused_segment (lo := 26352) (count := 32) (by decide +kernel)

private theorem rowsAt26384 : Checked rowOK 26384 26416 :=
  Checked.of_fused_segment (lo := 26384) (count := 32) (by decide +kernel)

private theorem rowsAt26416 : Checked rowOK 26416 26448 :=
  Checked.of_fused_segment (lo := 26416) (count := 32) (by decide +kernel)

private theorem rowsAt26448 : Checked rowOK 26448 26480 :=
  Checked.of_fused_segment (lo := 26448) (count := 32) (by decide +kernel)

private theorem rowsAt26480 : Checked rowOK 26480 26512 :=
  Checked.of_fused_segment (lo := 26480) (count := 32) (by decide +kernel)

private theorem rowsAt26512 : Checked rowOK 26512 26544 :=
  Checked.of_fused_segment (lo := 26512) (count := 32) (by decide +kernel)

private theorem rowsAt26544 : Checked rowOK 26544 26576 :=
  Checked.of_fused_segment (lo := 26544) (count := 32) (by decide +kernel)

private theorem rowsAt26576 : Checked rowOK 26576 26608 :=
  Checked.of_fused_segment (lo := 26576) (count := 32) (by decide +kernel)

private theorem rowsAt26608 : Checked rowOK 26608 26640 :=
  Checked.of_fused_segment (lo := 26608) (count := 32) (by decide +kernel)

private theorem rowsAt26640 : Checked rowOK 26640 26672 :=
  Checked.of_fused_segment (lo := 26640) (count := 32) (by decide +kernel)

private theorem rowsAt26672 : Checked rowOK 26672 26704 :=
  Checked.of_fused_segment (lo := 26672) (count := 32) (by decide +kernel)

private theorem rowsAt26704 : Checked rowOK 26704 26736 :=
  Checked.of_fused_segment (lo := 26704) (count := 32) (by decide +kernel)

private theorem rowsAt26736 : Checked rowOK 26736 26768 :=
  Checked.of_fused_segment (lo := 26736) (count := 32) (by decide +kernel)

private theorem rowsAt26768 : Checked rowOK 26768 26800 :=
  Checked.of_fused_segment (lo := 26768) (count := 32) (by decide +kernel)

private theorem rowsAt26800 : Checked rowOK 26800 26832 :=
  Checked.of_fused_segment (lo := 26800) (count := 32) (by decide +kernel)

private theorem rowsAt26832 : Checked rowOK 26832 26864 :=
  Checked.of_fused_segment (lo := 26832) (count := 32) (by decide +kernel)

private theorem rowsAt26864 : Checked rowOK 26864 26896 :=
  Checked.of_fused_segment (lo := 26864) (count := 32) (by decide +kernel)

private theorem rowsAt26896 : Checked rowOK 26896 26928 :=
  Checked.of_fused_segment (lo := 26896) (count := 32) (by decide +kernel)

private theorem rowsAt26928 : Checked rowOK 26928 26960 :=
  Checked.of_fused_segment (lo := 26928) (count := 32) (by decide +kernel)

private theorem rowsAt26960 : Checked rowOK 26960 26992 :=
  Checked.of_fused_segment (lo := 26960) (count := 32) (by decide +kernel)

private theorem rowsAt26992 : Checked rowOK 26992 27000 :=
  Checked.of_fused_segment (lo := 26992) (count := 8) (by decide +kernel)

theorem rowsFrom26000 : Checked rowOK 26000 27000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt26000 rowsAt26032) (Checked.join rowsAt26064 rowsAt26096)) (Checked.join (Checked.join rowsAt26128 rowsAt26160) (Checked.join rowsAt26192 rowsAt26224))) (Checked.join (Checked.join (Checked.join rowsAt26256 rowsAt26288) (Checked.join rowsAt26320 rowsAt26352)) (Checked.join (Checked.join rowsAt26384 rowsAt26416) (Checked.join rowsAt26448 rowsAt26480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt26512 rowsAt26544) (Checked.join rowsAt26576 rowsAt26608)) (Checked.join (Checked.join rowsAt26640 rowsAt26672) (Checked.join rowsAt26704 rowsAt26736))) (Checked.join (Checked.join (Checked.join rowsAt26768 rowsAt26800) (Checked.join rowsAt26832 rowsAt26864)) (Checked.join (Checked.join rowsAt26896 rowsAt26928) (Checked.join rowsAt26960 rowsAt26992)))))

end GaussianChains.Point22.Atlas.Tables
