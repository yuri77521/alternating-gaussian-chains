import Point22AtlasTablesPart31

/-! All 128001 samples and all 32000 rows now have a kernel-checked
connection to the actual periodized Gaussian and its two spatial derivatives. -/
namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains GaussianChains.ImageBounds

theorem allSamples : Checked traceOK 0 2000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join bandsFrom0 bandsFrom62) (Checked.join bandsFrom125 bandsFrom187)) (Checked.join (Checked.join bandsFrom250 bandsFrom312) (Checked.join bandsFrom375 bandsFrom437))) (Checked.join (Checked.join (Checked.join bandsFrom500 bandsFrom562) (Checked.join bandsFrom625 bandsFrom687)) (Checked.join (Checked.join bandsFrom750 bandsFrom812) (Checked.join bandsFrom875 bandsFrom937)))) (Checked.join (Checked.join (Checked.join (Checked.join bandsFrom1000 bandsFrom1062) (Checked.join bandsFrom1125 bandsFrom1187)) (Checked.join (Checked.join bandsFrom1250 bandsFrom1312) (Checked.join bandsFrom1375 bandsFrom1437))) (Checked.join (Checked.join (Checked.join bandsFrom1500 bandsFrom1562) (Checked.join bandsFrom1625 bandsFrom1687)) (Checked.join (Checked.join bandsFrom1750 bandsFrom1812) (Checked.join bandsFrom1875 bandsFrom1937)))))

theorem allRows : Checked rowOK 0 32000 :=
  (Checked.join (Checked.join (Checked.join (Checked.join (Checked.join rowsFrom0 rowsFrom1000) (Checked.join rowsFrom2000 rowsFrom3000)) (Checked.join (Checked.join rowsFrom4000 rowsFrom5000) (Checked.join rowsFrom6000 rowsFrom7000))) (Checked.join (Checked.join (Checked.join rowsFrom8000 rowsFrom9000) (Checked.join rowsFrom10000 rowsFrom11000)) (Checked.join (Checked.join rowsFrom12000 rowsFrom13000) (Checked.join rowsFrom14000 rowsFrom15000)))) (Checked.join (Checked.join (Checked.join (Checked.join rowsFrom16000 rowsFrom17000) (Checked.join rowsFrom18000 rowsFrom19000)) (Checked.join (Checked.join rowsFrom20000 rowsFrom21000) (Checked.join rowsFrom22000 rowsFrom23000))) (Checked.join (Checked.join (Checked.join rowsFrom24000 rowsFrom25000) (Checked.join rowsFrom26000 rowsFrom27000)) (Checked.join (Checked.join rowsFrom28000 rowsFrom29000) (Checked.join rowsFrom30000 rowsFrom31000)))))

theorem verifiedRow_eq_gridNode (j : Order) {p : ℕ} (hp : p < 32000) :
    (verifiedRow j p).decode unit = GaussianChains.Cert.Tables.gridNode work unit grid 22 j p :=
  verifiedRow_eq_gridNode_of_checks allSamples allRows j hp

theorem verifiedRow_sound (j : Order) {p : ℕ} (hp : p < 32000) :
    ((verifiedRow j p).decode unit).Mem
      ((deriv^[orderIndex j] (kernel 22)) ((p:ℝ)/32000)) :=
  verifiedRow_sound_of_checks allSamples allRows j hp

#print axioms verifiedRow_sound
end GaussianChains.Point22.Atlas.Tables
