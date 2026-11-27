import Point22AtlasTablesPart17

/-! Generated kernel proof obligations; see point22_atlas_tables_proofs.py. -/
namespace GaussianChains.Point22.Atlas.Tables
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

private theorem bandsAt1125 : Checked traceOK 1125 1129 :=
  Checked.of_segment (lo := 1125) (count := 4) (by decide +kernel)

private theorem bandsAt1129 : Checked traceOK 1129 1133 :=
  Checked.of_segment (lo := 1129) (count := 4) (by decide +kernel)

private theorem bandsAt1133 : Checked traceOK 1133 1137 :=
  Checked.of_segment (lo := 1133) (count := 4) (by decide +kernel)

private theorem bandsAt1137 : Checked traceOK 1137 1141 :=
  Checked.of_segment (lo := 1137) (count := 4) (by decide +kernel)

private theorem bandsAt1141 : Checked traceOK 1141 1145 :=
  Checked.of_segment (lo := 1141) (count := 4) (by decide +kernel)

private theorem bandsAt1145 : Checked traceOK 1145 1149 :=
  Checked.of_segment (lo := 1145) (count := 4) (by decide +kernel)

private theorem bandsAt1149 : Checked traceOK 1149 1153 :=
  Checked.of_segment (lo := 1149) (count := 4) (by decide +kernel)

private theorem bandsAt1153 : Checked traceOK 1153 1157 :=
  Checked.of_segment (lo := 1153) (count := 4) (by decide +kernel)

private theorem bandsAt1157 : Checked traceOK 1157 1161 :=
  Checked.of_segment (lo := 1157) (count := 4) (by decide +kernel)

private theorem bandsAt1161 : Checked traceOK 1161 1165 :=
  Checked.of_segment (lo := 1161) (count := 4) (by decide +kernel)

private theorem bandsAt1165 : Checked traceOK 1165 1169 :=
  Checked.of_segment (lo := 1165) (count := 4) (by decide +kernel)

private theorem bandsAt1169 : Checked traceOK 1169 1173 :=
  Checked.of_segment (lo := 1169) (count := 4) (by decide +kernel)

private theorem bandsAt1173 : Checked traceOK 1173 1177 :=
  Checked.of_segment (lo := 1173) (count := 4) (by decide +kernel)

private theorem bandsAt1177 : Checked traceOK 1177 1181 :=
  Checked.of_segment (lo := 1177) (count := 4) (by decide +kernel)

private theorem bandsAt1181 : Checked traceOK 1181 1185 :=
  Checked.of_segment (lo := 1181) (count := 4) (by decide +kernel)

private theorem bandsAt1185 : Checked traceOK 1185 1187 :=
  Checked.of_segment (lo := 1185) (count := 2) (by decide +kernel)

theorem bandsFrom1125 : Checked traceOK 1125 1187 :=
  (Checked.join (Checked.join (Checked.join (Checked.join bandsAt1125 bandsAt1129) (Checked.join bandsAt1133 bandsAt1137)) (Checked.join (Checked.join bandsAt1141 bandsAt1145) (Checked.join bandsAt1149 bandsAt1153))) (Checked.join (Checked.join (Checked.join bandsAt1157 bandsAt1161) (Checked.join bandsAt1165 bandsAt1169)) (Checked.join (Checked.join bandsAt1173 bandsAt1177) (Checked.join bandsAt1181 bandsAt1185))))

private theorem rowsAt18000 : Checked rowOK 18000 18032 :=
  Checked.of_fused_segment (lo := 18000) (count := 32) (by decide +kernel)

private theorem rowsAt18032 : Checked rowOK 18032 18064 :=
  Checked.of_fused_segment (lo := 18032) (count := 32) (by decide +kernel)

private theorem rowsAt18064 : Checked rowOK 18064 18096 :=
  Checked.of_fused_segment (lo := 18064) (count := 32) (by decide +kernel)

private theorem rowsAt18096 : Checked rowOK 18096 18128 :=
  Checked.of_fused_segment (lo := 18096) (count := 32) (by decide +kernel)

private theorem rowsAt18128 : Checked rowOK 18128 18160 :=
  Checked.of_fused_segment (lo := 18128) (count := 32) (by decide +kernel)

private theorem rowsAt18160 : Checked rowOK 18160 18192 :=
  Checked.of_fused_segment (lo := 18160) (count := 32) (by decide +kernel)

private theorem rowsAt18192 : Checked rowOK 18192 18224 :=
  Checked.of_fused_segment (lo := 18192) (count := 32) (by decide +kernel)

private theorem rowsAt18224 : Checked rowOK 18224 18256 :=
  Checked.of_fused_segment (lo := 18224) (count := 32) (by decide +kernel)

private theorem rowsAt18256 : Checked rowOK 18256 18288 :=
  Checked.of_fused_segment (lo := 18256) (count := 32) (by decide +kernel)

private theorem rowsAt18288 : Checked rowOK 18288 18320 :=
  Checked.of_fused_segment (lo := 18288) (count := 32) (by decide +kernel)

private theorem rowsAt18320 : Checked rowOK 18320 18352 :=
  Checked.of_fused_segment (lo := 18320) (count := 32) (by decide +kernel)

private theorem rowsAt18352 : Checked rowOK 18352 18384 :=
  Checked.of_fused_segment (lo := 18352) (count := 32) (by decide +kernel)

private theorem rowsAt18384 : Checked rowOK 18384 18416 :=
  Checked.of_fused_segment (lo := 18384) (count := 32) (by decide +kernel)

private theorem rowsAt18416 : Checked rowOK 18416 18448 :=
  Checked.of_fused_segment (lo := 18416) (count := 32) (by decide +kernel)

private theorem rowsAt18448 : Checked rowOK 18448 18480 :=
  Checked.of_fused_segment (lo := 18448) (count := 32) (by decide +kernel)

private theorem rowsAt18480 : Checked rowOK 18480 18512 :=
  Checked.of_fused_segment (lo := 18480) (count := 32) (by decide +kernel)

private theorem rowsAt18512 : Checked rowOK 18512 18544 :=
  Checked.of_fused_segment (lo := 18512) (count := 32) (by decide +kernel)

private theorem rowsAt18544 : Checked rowOK 18544 18576 :=
  Checked.of_fused_segment (lo := 18544) (count := 32) (by decide +kernel)

private theorem rowsAt18576 : Checked rowOK 18576 18608 :=
  Checked.of_fused_segment (lo := 18576) (count := 32) (by decide +kernel)

private theorem rowsAt18608 : Checked rowOK 18608 18640 :=
  Checked.of_fused_segment (lo := 18608) (count := 32) (by decide +kernel)

private theorem rowsAt18640 : Checked rowOK 18640 18672 :=
  Checked.of_fused_segment (lo := 18640) (count := 32) (by decide +kernel)

private theorem rowsAt18672 : Checked rowOK 18672 18704 :=
  Checked.of_fused_segment (lo := 18672) (count := 32) (by decide +kernel)

private theorem rowsAt18704 : Checked rowOK 18704 18736 :=
  Checked.of_fused_segment (lo := 18704) (count := 32) (by decide +kernel)

private theorem rowsAt18736 : Checked rowOK 18736 18768 :=
  Checked.of_fused_segment (lo := 18736) (count := 32) (by decide +kernel)

private theorem rowsAt18768 : Checked rowOK 18768 18800 :=
  Checked.of_fused_segment (lo := 18768) (count := 32) (by decide +kernel)

private theorem rowsAt18800 : Checked rowOK 18800 18832 :=
  Checked.of_fused_segment (lo := 18800) (count := 32) (by decide +kernel)

private theorem rowsAt18832 : Checked rowOK 18832 18864 :=
  Checked.of_fused_segment (lo := 18832) (count := 32) (by decide +kernel)

private theorem rowsAt18864 : Checked rowOK 18864 18896 :=
  Checked.of_fused_segment (lo := 18864) (count := 32) (by decide +kernel)

private theorem rowsAt18896 : Checked rowOK 18896 18928 :=
  Checked.of_fused_segment (lo := 18896) (count := 32) (by decide +kernel)

private theorem rowsAt18928 : Checked rowOK 18928 18960 :=
  Checked.of_fused_segment (lo := 18928) (count := 32) (by decide +kernel)

private theorem rowsAt18960 : Checked rowOK 18960 18992 :=
  Checked.of_fused_segment (lo := 18960) (count := 32) (by decide +kernel)

private theorem rowsAt18992 : Checked rowOK 18992 19000 :=
  Checked.of_fused_segment (lo := 18992) (count := 8) (by decide +kernel)

theorem rowsFrom18000 : Checked rowOK 18000 19000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsAt18000 rowsAt18032) (Checked.join rowsAt18064 rowsAt18096)) (Checked.join (Checked.join rowsAt18128 rowsAt18160) (Checked.join rowsAt18192 rowsAt18224))) (Checked.join (Checked.join (Checked.join rowsAt18256 rowsAt18288) (Checked.join rowsAt18320 rowsAt18352)) (Checked.join (Checked.join rowsAt18384 rowsAt18416) (Checked.join rowsAt18448 rowsAt18480)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsAt18512 rowsAt18544) (Checked.join rowsAt18576 rowsAt18608)) (Checked.join (Checked.join rowsAt18640 rowsAt18672) (Checked.join rowsAt18704 rowsAt18736))) (Checked.join (Checked.join (Checked.join rowsAt18768 rowsAt18800) (Checked.join rowsAt18832 rowsAt18864)) (Checked.join (Checked.join rowsAt18896 rowsAt18928) (Checked.join rowsAt18960 rowsAt18992)))))

end GaussianChains.Point22.Atlas.Tables
