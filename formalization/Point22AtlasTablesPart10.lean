import Point22AtlasTablesPart09

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt625 : Checked traceOK 625 629 :=
  Checked.of_segment (lo := 625) (count := 4) (by decide +kernel)

private theorem bandsAt629 : Checked traceOK 629 633 :=
  Checked.of_segment (lo := 629) (count := 4) (by decide +kernel)

private theorem bandsAt633 : Checked traceOK 633 637 :=
  Checked.of_segment (lo := 633) (count := 4) (by decide +kernel)

private theorem bandsAt637 : Checked traceOK 637 641 :=
  Checked.of_segment (lo := 637) (count := 4) (by decide +kernel)

private theorem bandsAt641 : Checked traceOK 641 645 :=
  Checked.of_segment (lo := 641) (count := 4) (by decide +kernel)

private theorem bandsAt645 : Checked traceOK 645 649 :=
  Checked.of_segment (lo := 645) (count := 4) (by decide +kernel)

private theorem bandsAt649 : Checked traceOK 649 653 :=
  Checked.of_segment (lo := 649) (count := 4) (by decide +kernel)

private theorem bandsAt653 : Checked traceOK 653 657 :=
  Checked.of_segment (lo := 653) (count := 4) (by decide +kernel)

private theorem bandsAt657 : Checked traceOK 657 661 :=
  Checked.of_segment (lo := 657) (count := 4) (by decide +kernel)

private theorem bandsAt661 : Checked traceOK 661 665 :=
  Checked.of_segment (lo := 661) (count := 4) (by decide +kernel)

private theorem bandsAt665 : Checked traceOK 665 669 :=
  Checked.of_segment (lo := 665) (count := 4) (by decide +kernel)

private theorem bandsAt669 : Checked traceOK 669 673 :=
  Checked.of_segment (lo := 669) (count := 4) (by decide +kernel)

private theorem bandsAt673 : Checked traceOK 673 677 :=
  Checked.of_segment (lo := 673) (count := 4) (by decide +kernel)

private theorem bandsAt677 : Checked traceOK 677 681 :=
  Checked.of_segment (lo := 677) (count := 4) (by decide +kernel)

private theorem bandsAt681 : Checked traceOK 681 685 :=
  Checked.of_segment (lo := 681) (count := 4) (by decide +kernel)

private theorem bandsAt685 : Checked traceOK 685 687 :=
  Checked.of_segment (lo := 685) (count := 2) (by decide +kernel)

theorem bandsFrom625 : Checked traceOK 625 687 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt625 bandsAt629) (Checked.join bandsAt633 bandsAt637)) (Checked.join (Checked.join bandsAt641 bandsAt645) (Checked.join bandsAt649 bandsAt653))) (Checked.join (Checked.join (Checked.join bandsAt657 bandsAt661) (Checked.join bandsAt665 bandsAt669)) (Checked.join (Checked.join bandsAt673 bandsAt677) (Checked.join bandsAt681 bandsAt685))))

private theorem rowsAt10000 : Checked rowOK 10000 10032 :=
  Checked.of_fused_segment (lo := 10000) (count := 32) (by decide +kernel)

private theorem rowsAt10032 : Checked rowOK 10032 10064 :=
  Checked.of_fused_segment (lo := 10032) (count := 32) (by decide +kernel)

private theorem rowsAt10064 : Checked rowOK 10064 10096 :=
  Checked.of_fused_segment (lo := 10064) (count := 32) (by decide +kernel)

private theorem rowsAt10096 : Checked rowOK 10096 10128 :=
  Checked.of_fused_segment (lo := 10096) (count := 32) (by decide +kernel)

private theorem rowsAt10128 : Checked rowOK 10128 10160 :=
  Checked.of_fused_segment (lo := 10128) (count := 32) (by decide +kernel)

private theorem rowsAt10160 : Checked rowOK 10160 10192 :=
  Checked.of_fused_segment (lo := 10160) (count := 32) (by decide +kernel)

private theorem rowsAt10192 : Checked rowOK 10192 10224 :=
  Checked.of_fused_segment (lo := 10192) (count := 32) (by decide +kernel)

private theorem rowsAt10224 : Checked rowOK 10224 10256 :=
  Checked.of_fused_segment (lo := 10224) (count := 32) (by decide +kernel)

private theorem rowsAt10256 : Checked rowOK 10256 10288 :=
  Checked.of_fused_segment (lo := 10256) (count := 32) (by decide +kernel)

private theorem rowsAt10288 : Checked rowOK 10288 10320 :=
  Checked.of_fused_segment (lo := 10288) (count := 32) (by decide +kernel)

private theorem rowsAt10320 : Checked rowOK 10320 10352 :=
  Checked.of_fused_segment (lo := 10320) (count := 32) (by decide +kernel)

private theorem rowsAt10352 : Checked rowOK 10352 10384 :=
  Checked.of_fused_segment (lo := 10352) (count := 32) (by decide +kernel)

private theorem rowsAt10384 : Checked rowOK 10384 10416 :=
  Checked.of_fused_segment (lo := 10384) (count := 32) (by decide +kernel)

private theorem rowsAt10416 : Checked rowOK 10416 10448 :=
  Checked.of_fused_segment (lo := 10416) (count := 32) (by decide +kernel)

private theorem rowsAt10448 : Checked rowOK 10448 10480 :=
  Checked.of_fused_segment (lo := 10448) (count := 32) (by decide +kernel)

private theorem rowsAt10480 : Checked rowOK 10480 10512 :=
  Checked.of_fused_segment (lo := 10480) (count := 32) (by decide +kernel)

private theorem rowsAt10512 : Checked rowOK 10512 10544 :=
  Checked.of_fused_segment (lo := 10512) (count := 32) (by decide +kernel)

private theorem rowsAt10544 : Checked rowOK 10544 10576 :=
  Checked.of_fused_segment (lo := 10544) (count := 32) (by decide +kernel)

private theorem rowsAt10576 : Checked rowOK 10576 10608 :=
  Checked.of_fused_segment (lo := 10576) (count := 32) (by decide +kernel)

private theorem rowsAt10608 : Checked rowOK 10608 10640 :=
  Checked.of_fused_segment (lo := 10608) (count := 32) (by decide +kernel)

private theorem rowsAt10640 : Checked rowOK 10640 10672 :=
  Checked.of_fused_segment (lo := 10640) (count := 32) (by decide +kernel)

private theorem rowsAt10672 : Checked rowOK 10672 10704 :=
  Checked.of_fused_segment (lo := 10672) (count := 32) (by decide +kernel)

private theorem rowsAt10704 : Checked rowOK 10704 10736 :=
  Checked.of_fused_segment (lo := 10704) (count := 32) (by decide +kernel)

private theorem rowsAt10736 : Checked rowOK 10736 10768 :=
  Checked.of_fused_segment (lo := 10736) (count := 32) (by decide +kernel)

private theorem rowsAt10768 : Checked rowOK 10768 10800 :=
  Checked.of_fused_segment (lo := 10768) (count := 32) (by decide +kernel)

private theorem rowsAt10800 : Checked rowOK 10800 10832 :=
  Checked.of_fused_segment (lo := 10800) (count := 32) (by decide +kernel)

private theorem rowsAt10832 : Checked rowOK 10832 10864 :=
  Checked.of_fused_segment (lo := 10832) (count := 32) (by decide +kernel)

private theorem rowsAt10864 : Checked rowOK 10864 10896 :=
  Checked.of_fused_segment (lo := 10864) (count := 32) (by decide +kernel)

private theorem rowsAt10896 : Checked rowOK 10896 10928 :=
  Checked.of_fused_segment (lo := 10896) (count := 32) (by decide +kernel)

private theorem rowsAt10928 : Checked rowOK 10928 10960 :=
  Checked.of_fused_segment (lo := 10928) (count := 32) (by decide +kernel)

private theorem rowsAt10960 : Checked rowOK 10960 10992 :=
  Checked.of_fused_segment (lo := 10960) (count := 32) (by decide +kernel)

private theorem rowsAt10992 : Checked rowOK 10992 11000 :=
  Checked.of_fused_segment (lo := 10992) (count := 8) (by decide +kernel)

theorem rowsFrom10000 : Checked rowOK 10000 11000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt10000 rowsAt10032) (Checked.join rowsAt10064 rowsAt10096)) (Checked.join (Checked.join rowsAt10128 rowsAt10160) (Checked.join rowsAt10192 rowsAt10224))) (Checked.join (Checked.join (Checked.join rowsAt10256 rowsAt10288) (Checked.join rowsAt10320 rowsAt10352)) (Checked.join (Checked.join rowsAt10384 rowsAt10416) (Checked.join rowsAt10448 rowsAt10480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt10512 rowsAt10544) (Checked.join rowsAt10576 rowsAt10608)) (Checked.join (Checked.join rowsAt10640 rowsAt10672) (Checked.join rowsAt10704 rowsAt10736))) (Checked.join (Checked.join (Checked.join rowsAt10768 rowsAt10800) (Checked.join rowsAt10832 rowsAt10864)) (Checked.join (Checked.join rowsAt10896 rowsAt10928) (Checked.join rowsAt10960 rowsAt10992)))))

end GaussianChains.Point22.Atlas.Tables
