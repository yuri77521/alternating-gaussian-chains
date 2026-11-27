import Point22AtlasRangeGroup111Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf111

private abbrev get := fastBlock verifiedRow 1 1 .first
private theorem get_eq_raw : get = rawBlock verifiedRow 1 1 .first :=
  funext (fastBlock_eq_raw verifiedRow 1 1 .first)

private theorem s512_512 : Run get 512 512 ⟨-137535126554,-70004619814⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

private theorem s1024_512 : Run get 1024 512 ⟨-200644007678,-137663515117⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

theorem claim13 : CheckedClaim verifiedRow ⟨1,1,1,32,2020,-254437847105,-4399884783⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 32 1989 ⟨-254437828794,-4399903094⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_512 (by decide)) (append (widen s1536_256 (by decide)) (append (widen s1792_128 (by decide)) (append (widen s1920_64 (by decide)) (append (widen s1984_32 (by decide)) (append (widen s2016_4 (by decide)) (widen s2020_1 (by decide)))))))))))))

private theorem s1536_512 : Run get 1536 512 ⟨-257231159638,-200761473995⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨-257231159638,-137663515117⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

private theorem s2048_512 : Run get 2048 512 ⟨-305683528027,-257334181256⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

theorem claim14 : CheckedClaim verifiedRow ⟨1,1,1,32,3014,-340945836846,-4399884783⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 32 2983 ⟨-340945818535,-4399903094⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_512 (by decide)) (append (widen s2560_256 (by decide)) (append (widen s2816_128 (by decide)) (append (widen s2944_64 (by decide)) (append (widen s3008_4 (by decide)) (append (widen s3012_2 (by decide)) (widen s3014_1 (by decide))))))))))))))

private theorem s2560_512 : Run get 2560 512 ⟨-344814626416,-305769352374⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨-344814626416,-257334181256⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨-373908093854,-344881387308⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

theorem claim15 : CheckedClaim verifiedRow ⟨1,1,1,32,4008,-390250745945,-4399884783⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 32 3977 ⟨-390250727634,-4399903094⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_32 (by decide)) (append (widen s4000_8 (by decide)) (widen s4008_1 (by decide))))))))))))))

private theorem s3584_512 : Run get 3584 512 ⟨-392728323067,-373954864434⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨-392728323067,-344881387308⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

private theorem s2048_2048 : Run get 2048 2048 ⟨-392728323067,-257334181256⟩ :=
  join s2048_1024 s3072_1024 (by decide) (by decide)

private theorem s4096_512 : Run get 4096 512 ⟨-401499322728,-392755104646⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

private theorem s4608_512 : Run get 4608 512 ⟨-402326443510,-400855628368⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨-402326443510,-392755104646⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨-400845747864,-391771174800⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

theorem claim16 : CheckedClaim verifiedRow ⟨1,1,1,32,5996,-402326461821,-4399884783⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 32 5965 ⟨-402326443510,-4399903094⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide))))))))))))))))

private theorem s5632_512 : Run get 5632 512 ⟨-391745941859,-375473406491⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨-400845747864,-375473406491⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨-402326443510,-375473406491⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨-375435406275,-353350449688⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨-353302489611,-326858921077⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨-375435406275,-326858921077⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨-326803855917,-297439012539⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim17 : CheckedClaim verifiedRow ⟨1,1,1,32,7984,-402326461821,-4399884783⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 32 7953 ⟨-402326443510,-4399903094⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))))))))))

theorem claim18 : CheckedClaim verifiedRow ⟨1,1,1,64,2052,-257745974154,-8799207110⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 64 1989 ⟨-257745955843,-8799225421⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide))))))))

theorem claim19 : CheckedClaim verifiedRow ⟨1,1,1,64,4040,-391196026854,-8799207110⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 64 3977 ⟨-391196008543,-8799225421⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))

theorem claim20 : CheckedClaim verifiedRow ⟨1,1,1,64,6028,-402326461821,-8799207110⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 64 5965 ⟨-402326443510,-8799225421⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide))))))))))))))

theorem claim21 : CheckedClaim verifiedRow ⟨1,1,1,96,4072,-392101741679,-13197368029⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 96 3977 ⟨-392101723368,-13197386340⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide))))))))))))))

theorem claim22 : CheckedClaim verifiedRow ⟨1,1,1,2020,4008,-390250745945,-254437810480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2020 1989 ⟨-390250727634,-254437828791⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_32 (by decide)) (append (widen s4000_8 (by decide)) (widen s4008_1 (by decide)))))))))))

theorem claim23 : CheckedClaim verifiedRow ⟨1,1,1,2020,5002,-402326461821,-254437810480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2020 2983 ⟨-402326443510,-254437828791⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_8 (by decide)) (append (widen s5000_2 (by decide)) (widen s5002_1 (by decide)))))))))))

theorem claim24 : CheckedClaim verifiedRow ⟨1,1,1,2020,5996,-402326461821,-254437810480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2020 3977 ⟨-402326443510,-254437828791⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide)))))))))))))

theorem claim25 : CheckedClaim verifiedRow ⟨1,1,1,2020,7984,-402326461821,-254437810480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2020 5965 ⟨-402326443510,-254437828791⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))))))

theorem claim26 : CheckedClaim verifiedRow ⟨1,1,1,2052,4040,-391196026854,-257745937529⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2052 1989 ⟨-391196008543,-257745955840⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))))

theorem claim27 : CheckedClaim verifiedRow ⟨1,1,1,2052,6028,-402326461821,-257745937529⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2052 3977 ⟨-402326443510,-257745955840⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide)))))))))))))))))

theorem claim28 : CheckedClaim verifiedRow ⟨1,1,1,2052,8016,-402326461821,-257745937529⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2052 5965 ⟨-402326443510,-257745955840⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))))))))

theorem claim29 : CheckedClaim verifiedRow ⟨1,1,1,2084,4072,-392101741679,-261022094512⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2084 1989 ⟨-392101723368,-261022112823⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide)))))))))))))))

theorem claim30 : CheckedClaim verifiedRow ⟨1,1,1,2084,6060,-402326461821,-261022094512⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2084 3977 ⟨-402326443510,-261022112823⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))))))))

theorem claim31 : CheckedClaim verifiedRow ⟨1,1,1,2084,8048,-402326461821,-261022094512⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2084 5965 ⟨-402326443510,-261022112823⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))))))))

theorem claim32 : CheckedClaim verifiedRow ⟨1,1,1,2116,4104,-392967991232,-264265940377⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2116 1989 ⟨-392967972921,-264265958688⟩
  rw [← get_eq_raw]
  exact (append (widen s2116_4 (by decide)) (append (widen s2120_8 (by decide)) (append (widen s2128_16 (by decide)) (append (widen s2144_32 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_8 (by decide)) (widen s4104_1 (by decide)))))))))))

theorem claim33 : CheckedClaim verifiedRow ⟨1,1,1,2116,8080,-402326461821,-264265940377⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 2116 5965 ⟨-402326443510,-264265958688⟩
  rw [← get_eq_raw]
  exact (append (widen s2116_4 (by decide)) (append (widen s2120_8 (by decide)) (append (widen s2128_16 (by decide)) (append (widen s2144_32 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide))))))))))))))))

theorem claim34 : CheckedClaim verifiedRow ⟨1,1,1,3014,4505,-400528566867,-340945800221⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 3014 1492 ⟨-400528548556,-340945818532⟩
  rw [← get_eq_raw]
  exact (append (widen s3014_2 (by decide)) (append (widen s3016_8 (by decide)) (append (widen s3024_16 (by decide)) (append (widen s3040_32 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_256 (by decide)) (append (widen s4352_128 (by decide)) (append (widen s4480_16 (by decide)) (append (widen s4496_8 (by decide)) (widen s4504_2 (by decide)))))))))))

theorem claim35 : CheckedClaim verifiedRow ⟨1,1,1,3014,5002,-402326461821,-340945800221⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 3014 1989 ⟨-402326443510,-340945818532⟩
  rw [← get_eq_raw]
  exact (append (widen s3014_2 (by decide)) (append (widen s3016_8 (by decide)) (append (widen s3024_16 (by decide)) (append (widen s3040_32 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_8 (by decide)) (append (widen s5000_2 (by decide)) (widen s5002_1 (by decide))))))))))))

theorem claim36 : CheckedClaim verifiedRow ⟨1,1,1,3014,5996,-402326461821,-340945800221⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 3014 2983 ⟨-402326443510,-340945818532⟩
  rw [← get_eq_raw]
  exact (append (widen s3014_2 (by decide)) (append (widen s3016_8 (by decide)) (append (widen s3024_16 (by decide)) (append (widen s3040_32 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide))))))))))))))

theorem claim37 : CheckedClaim verifiedRow ⟨1,1,1,4008,5002,-402326461821,-390250709320⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4008 995 ⟨-402326443510,-390250727631⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_8 (by decide)) (append (widen s5000_2 (by decide)) (widen s5002_1 (by decide))))))))))

theorem claim38 : CheckedClaim verifiedRow ⟨1,1,1,4008,5996,-402326461821,-380811784976⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4008 1989 ⟨-402326443510,-380811803287⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide))))))))))))

theorem claim39 : CheckedClaim verifiedRow ⟨1,1,1,4008,6990,-402326461821,-336420143183⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4008 2983 ⟨-402326443510,-336420161494⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_64 (by decide)) (append (widen s6976_8 (by decide)) (append (widen s6984_4 (by decide)) (append (widen s6988_2 (by decide)) (widen s6990_1 (by decide))))))))))))

theorem claim40 : CheckedClaim verifiedRow ⟨1,1,1,4008,7984,-402326461821,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4008 3977 ⟨-402326443510,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))))))

private theorem s7680_512 : Run get 7680 512 ⟨-297379589366,-266442045917⟩ :=
  join s7680_256 s7936_256 (by decide) (by decide)

private theorem s7168_1024 : Run get 7168 1024 ⟨-326803855917,-266442045917⟩ :=
  join s7168_512 s7680_512 (by decide) (by decide)

private theorem s6144_2048 : Run get 6144 2048 ⟨-375435406275,-266442045917⟩ :=
  join s6144_1024 s7168_1024 (by decide) (by decide)

private theorem s4096_4096 : Run get 4096 4096 ⟨-402326443510,-266442045917⟩ :=
  join s4096_2048 s6144_2048 (by decide) (by decide)

private theorem s8192_512 : Run get 8192 512 ⟨-266380777358,-235073948922⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

private theorem s8704_512 : Run get 8704 512 ⟨-235013019689,-204356282012⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨-266380777358,-204356282012⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨-204297490166,-175104743662⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

theorem claim41 : CheckedClaim verifiedRow ⟨1,1,1,4008,9972,-402326461821,-161810581645⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4008 5965 ⟨-402326443510,-161810599956⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide)))))))))))))

theorem claim42 : CheckedClaim verifiedRow ⟨1,1,1,4040,6028,-402326461821,-379692333103⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4040 1989 ⟨-402326443510,-379692351414⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide)))))))))))

theorem claim43 : CheckedClaim verifiedRow ⟨1,1,1,4040,7022,-402326461821,-334720045250⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4040 2983 ⟨-402326443510,-334720063561⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_64 (by decide)) (append (widen s6976_32 (by decide)) (append (widen s7008_8 (by decide)) (append (widen s7016_4 (by decide)) (append (widen s7020_2 (by decide)) (widen s7022_1 (by decide)))))))))))))

theorem claim44 : CheckedClaim verifiedRow ⟨1,1,1,4040,8016,-402326461821,-277135570529⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4040 3977 ⟨-402326443510,-277135588840⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim45 : CheckedClaim verifiedRow ⟨1,1,1,4040,10004,-402326461821,-160112141240⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4040 5965 ⟨-402326443510,-160112159551⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide)))))))))))

theorem claim46 : CheckedClaim verifiedRow ⟨1,1,1,4072,6060,-402326461821,-378548844335⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4072 1989 ⟨-402326443510,-378548862646⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))

theorem claim47 : CheckedClaim verifiedRow ⟨1,1,1,4072,8048,-402326461821,-275185348322⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4072 3977 ⟨-402326443510,-275185366633⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim48 : CheckedClaim verifiedRow ⟨1,1,1,4072,10036,-402326461821,-158422794072⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4072 5965 ⟨-402326443510,-158422812383⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide)))))))))))

theorem claim49 : CheckedClaim verifiedRow ⟨1,1,1,4104,8080,-402326461821,-273232485558⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4104 3977 ⟨-402326443510,-273232503869⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide)))))))))))))))

theorem claim50 : CheckedClaim verifiedRow ⟨1,1,1,4104,10068,-402326461821,-156742633974⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4104 5965 ⟨-402326443510,-156742652285⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_64 (by decide)) (append (widen s10048_16 (by decide)) (append (widen s10064_4 (by decide)) (widen s10068_1 (by decide)))))))))))))))))

theorem claim51 : CheckedClaim verifiedRow ⟨1,1,1,4136,8112,-402326461821,-271277267083⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 4136 3977 ⟨-402326443510,-271277285394⟩
  rw [← get_eq_raw]
  exact (append (widen s4136_8 (by decide)) (append (widen s4144_16 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_16 (by decide)) (widen s8112_1 (by decide)))))))))))))))

theorem claim52 : CheckedClaim verifiedRow ⟨1,1,1,5002,5996,-401786633633,-380811784976⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5002 995 ⟨-401786615322,-380811803287⟩
  rw [← get_eq_raw]
  exact (append (widen s5002_2 (by decide)) (append (widen s5004_4 (by decide)) (append (widen s5008_16 (by decide)) (append (widen s5024_32 (by decide)) (append (widen s5056_64 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide)))))))))))))

theorem claim53 : CheckedClaim verifiedRow ⟨1,1,1,5002,6990,-401786633633,-336420143183⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5002 1989 ⟨-401786615322,-336420161494⟩
  rw [← get_eq_raw]
  exact (append (widen s5002_2 (by decide)) (append (widen s5004_4 (by decide)) (append (widen s5008_16 (by decide)) (append (widen s5024_32 (by decide)) (append (widen s5056_64 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_64 (by decide)) (append (widen s6976_8 (by decide)) (append (widen s6984_4 (by decide)) (append (widen s6988_2 (by decide)) (widen s6990_1 (by decide))))))))))))))

theorem claim54 : CheckedClaim verifiedRow ⟨1,1,1,5002,7984,-401786633633,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5002 2983 ⟨-401786615322,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s5002_2 (by decide)) (append (widen s5004_4 (by decide)) (append (widen s5008_16 (by decide)) (append (widen s5024_32 (by decide)) (append (widen s5056_64 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))))))))

theorem claim55 : CheckedClaim verifiedRow ⟨1,1,1,5034,8016,-401576658599,-277135570529⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5034 2983 ⟨-401576640288,-277135588840⟩
  rw [← get_eq_raw]
  exact (append (widen s5034_2 (by decide)) (append (widen s5036_4 (by decide)) (append (widen s5040_16 (by decide)) (append (widen s5056_64 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide))))))))))))

theorem claim56 : CheckedClaim verifiedRow ⟨1,1,1,5996,6990,-380811821601,-336420143183⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5996 995 ⟨-380811803290,-336420161494⟩
  rw [← get_eq_raw]
  exact (append (widen s5996_4 (by decide)) (append (widen s6000_16 (by decide)) (append (widen s6016_128 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_64 (by decide)) (append (widen s6976_8 (by decide)) (append (widen s6984_4 (by decide)) (append (widen s6988_2 (by decide)) (widen s6990_1 (by decide)))))))))))

theorem claim57 : CheckedClaim verifiedRow ⟨1,1,1,5996,7487,-380811821601,-308726187718⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5996 1492 ⟨-380811803290,-308726206029⟩
  rw [← get_eq_raw]
  exact (append (widen s5996_4 (by decide)) (append (widen s6000_16 (by decide)) (append (widen s6016_128 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_256 (by decide)) (widen s7424_64 (by decide)))))))

theorem claim58 : CheckedClaim verifiedRow ⟨1,1,1,5996,7984,-380811821601,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5996 1989 ⟨-380811803290,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s5996_4 (by decide)) (append (widen s6000_16 (by decide)) (append (widen s6016_128 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))))

theorem claim59 : CheckedClaim verifiedRow ⟨1,1,1,5996,9972,-380811821601,-161810581645⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 5996 3977 ⟨-380811803290,-161810599956⟩
  rw [← get_eq_raw]
  exact (append (widen s5996_4 (by decide)) (append (widen s6000_16 (by decide)) (append (widen s6016_128 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide)))))))))))))

theorem claim60 : CheckedClaim verifiedRow ⟨1,1,1,6028,8016,-379692369728,-277135570529⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6028 1989 ⟨-379692351417,-277135588840⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim61 : CheckedClaim verifiedRow ⟨1,1,1,6028,10004,-379692369728,-160112141240⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6028 3977 ⟨-379692351417,-160112159551⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide))))))))))))

private theorem s9728_512 : Run get 9728 512 ⟨-175049474952,-147923652178⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨-204297490166,-147923652178⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨-266380777358,-147923652178⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨-147872883356,-123213846016⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨-123168171373,-101190803506⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨-147872883356,-101190803506⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨-101150478019,-81909546671⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

theorem claim62 : CheckedClaim verifiedRow ⟨1,1,1,6028,11992,-379692369728,-74550015650⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6028 5965 ⟨-379692351417,-74550033961⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))))

theorem claim63 : CheckedClaim verifiedRow ⟨1,1,1,6060,8048,-378548880960,-275185348322⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6060 1989 ⟨-378548862649,-275185366633⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim64 : CheckedClaim verifiedRow ⟨1,1,1,6060,9042,-378548880960,-214607773517⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6060 2983 ⟨-378548862649,-214607791828⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_512 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_64 (by decide)) (append (widen s9024_16 (by decide)) (append (widen s9040_2 (by decide)) (widen s9042_1 (by decide)))))))))))

theorem claim65 : CheckedClaim verifiedRow ⟨1,1,1,6060,12024,-378548880960,-73504665661⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6060 5965 ⟨-378548862649,-73504683972⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))))

theorem claim66 : CheckedClaim verifiedRow ⟨1,1,1,6092,8080,-377381704443,-273232485558⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6092 1989 ⟨-377381686132,-273232503869⟩
  rw [← get_eq_raw]
  exact (append (widen s6092_4 (by decide)) (append (widen s6096_16 (by decide)) (append (widen s6112_32 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide))))))))))

theorem claim67 : CheckedClaim verifiedRow ⟨1,1,1,6092,12056,-377381704443,-72469454810⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6092 5965 ⟨-377381686132,-72469473121⟩
  rw [← get_eq_raw]
  exact (append (widen s6092_4 (by decide)) (append (widen s6096_16 (by decide)) (append (widen s6112_32 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide))))))))))))

theorem claim68 : CheckedClaim verifiedRow ⟨1,1,1,6124,8112,-376191190580,-271277267083⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6124 1989 ⟨-376191172269,-271277285394⟩
  rw [← get_eq_raw]
  exact (append (widen s6124_4 (by decide)) (append (widen s6128_16 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_16 (by decide)) (widen s8112_1 (by decide))))))))))

theorem claim69 : CheckedClaim verifiedRow ⟨1,1,1,6493,7487,-360892294784,-308726187718⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6493 995 ⟨-360892276473,-308726206029⟩
  rw [← get_eq_raw]
  exact (append (widen s6493_1 (by decide)) (append (widen s6494_2 (by decide)) (append (widen s6496_32 (by decide)) (append (widen s6528_128 (by decide)) (append (widen s6656_512 (by decide)) (append (widen s7168_256 (by decide)) (widen s7424_64 (by decide))))))))

theorem claim70 : CheckedClaim verifiedRow ⟨1,1,1,6990,7736,-336420179808,-294042642414⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6990 747 ⟨-336420161497,-294042660725⟩
  rw [← get_eq_raw]
  exact (append (widen s6990_2 (by decide)) (append (widen s6992_16 (by decide)) (append (widen s7008_32 (by decide)) (append (widen s7040_128 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_32 (by decide)) (append (widen s7712_16 (by decide)) (append (widen s7728_8 (by decide)) (widen s7736_1 (by decide))))))))))

theorem claim71 : CheckedClaim verifiedRow ⟨1,1,1,6990,7984,-336420179808,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6990 995 ⟨-336420161497,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s6990_2 (by decide)) (append (widen s6992_16 (by decide)) (append (widen s7008_32 (by decide)) (append (widen s7040_128 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))))

theorem claim72 : CheckedClaim verifiedRow ⟨1,1,1,6990,8978,-336420179808,-218437440449⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 6990 1989 ⟨-336420161497,-218437458760⟩
  rw [← get_eq_raw]
  exact (append (widen s6990_2 (by decide)) (append (widen s6992_16 (by decide)) (append (widen s7008_32 (by decide)) (append (widen s7040_128 (by decide)) (append (widen s7168_1024 (by decide)) (append (widen s8192_512 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_16 (by decide)) (append (widen s8976_2 (by decide)) (widen s8978_1 (by decide)))))))))))

theorem claim73 : CheckedClaim verifiedRow ⟨1,1,1,7239,7735,-322866421610,-294102384574⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7239 497 ⟨-322866403299,-294102402885⟩
  rw [← get_eq_raw]
  exact (append (widen s7239_1 (by decide)) (append (widen s7240_8 (by decide)) (append (widen s7248_16 (by decide)) (append (widen s7264_32 (by decide)) (append (widen s7296_128 (by decide)) (append (widen s7424_256 (by decide)) (append (widen s7680_32 (by decide)) (append (widen s7712_16 (by decide)) (widen s7728_8 (by decide))))))))))

theorem claim74 : CheckedClaim verifiedRow ⟨1,1,1,7487,7859,-308726224343,-286655911364⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7487 373 ⟨-308726206032,-286655929675⟩
  rw [← get_eq_raw]
  exact (append (widen s7487_1 (by decide)) (append (widen s7488_64 (by decide)) (append (widen s7552_128 (by decide)) (append (widen s7680_128 (by decide)) (append (widen s7808_32 (by decide)) (append (widen s7840_16 (by decide)) (widen s7856_4 (by decide))))))))

theorem claim75 : CheckedClaim verifiedRow ⟨1,1,1,7487,7860,-308726224343,-286595568230⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7487 374 ⟨-308726206032,-286595586541⟩
  rw [← get_eq_raw]
  exact (append (widen s7487_1 (by decide)) (append (widen s7488_64 (by decide)) (append (widen s7552_128 (by decide)) (append (widen s7680_128 (by decide)) (append (widen s7808_32 (by decide)) (append (widen s7840_16 (by decide)) (append (widen s7856_4 (by decide)) (widen s7860_1 (by decide)))))))))

theorem claim76 : CheckedClaim verifiedRow ⟨1,1,1,7487,7984,-308726224343,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7487 498 ⟨-308726206032,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7487_1 (by decide)) (append (widen s7488_64 (by decide)) (append (widen s7552_128 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))

theorem claim77 : CheckedClaim verifiedRow ⟨1,1,1,7611,7860,-301465297736,-286595568230⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7611 250 ⟨-301465279425,-286595586541⟩
  rw [← get_eq_raw]
  exact (append (widen s7611_1 (by decide)) (append (widen s7612_4 (by decide)) (append (widen s7616_64 (by decide)) (append (widen s7680_128 (by decide)) (append (widen s7808_32 (by decide)) (append (widen s7840_16 (by decide)) (append (widen s7856_4 (by decide)) (widen s7860_1 (by decide)))))))))

theorem claim78 : CheckedClaim verifiedRow ⟨1,1,1,7611,7984,-301465297736,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7611 374 ⟨-301465279425,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7611_1 (by decide)) (append (widen s7612_4 (by decide)) (append (widen s7616_64 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))

theorem claim79 : CheckedClaim verifiedRow ⟨1,1,1,7612,7984,-301406302469,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7612 373 ⟨-301406284158,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7612_4 (by decide)) (append (widen s7616_64 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))

theorem claim80 : CheckedClaim verifiedRow ⟨1,1,1,7735,7921,-294102421199,-282906918177⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7735 187 ⟨-294102402888,-282906936488⟩
  rw [← get_eq_raw]
  exact (append (widen s7735_1 (by decide)) (append (widen s7736_8 (by decide)) (append (widen s7744_64 (by decide)) (append (widen s7808_64 (by decide)) (append (widen s7872_32 (by decide)) (append (widen s7904_16 (by decide)) (widen s7920_2 (by decide))))))))

theorem claim81 : CheckedClaim verifiedRow ⟨1,1,1,7735,7922,-294102421199,-282846327908⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7735 188 ⟨-294102402888,-282846346219⟩
  rw [← get_eq_raw]
  exact (append (widen s7735_1 (by decide)) (append (widen s7736_8 (by decide)) (append (widen s7744_64 (by decide)) (append (widen s7808_64 (by decide)) (append (widen s7872_32 (by decide)) (append (widen s7904_16 (by decide)) (append (widen s7920_2 (by decide)) (widen s7922_1 (by decide)))))))))

theorem claim82 : CheckedClaim verifiedRow ⟨1,1,1,7735,7984,-294102421199,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7735 250 ⟨-294102402888,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7735_1 (by decide)) (append (widen s7736_8 (by decide)) (append (widen s7744_64 (by decide)) (append (widen s7808_128 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))

theorem claim83 : CheckedClaim verifiedRow ⟨1,1,1,7736,7984,-294042679039,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7736 249 ⟨-294042660728,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7736_8 (by decide)) (append (widen s7744_64 (by decide)) (append (widen s7808_128 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))

theorem claim84 : CheckedClaim verifiedRow ⟨1,1,1,7797,7922,-290388507260,-282846327908⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7797 126 ⟨-290388488949,-282846346219⟩
  rw [← get_eq_raw]
  exact (append (widen s7797_1 (by decide)) (append (widen s7798_2 (by decide)) (append (widen s7800_8 (by decide)) (append (widen s7808_64 (by decide)) (append (widen s7872_32 (by decide)) (append (widen s7904_16 (by decide)) (append (widen s7920_2 (by decide)) (widen s7922_1 (by decide)))))))))

theorem claim85 : CheckedClaim verifiedRow ⟨1,1,1,7797,7984,-290388507260,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7797 188 ⟨-290388488949,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7797_1 (by decide)) (append (widen s7798_2 (by decide)) (append (widen s7800_8 (by decide)) (append (widen s7808_128 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))

theorem claim86 : CheckedClaim verifiedRow ⟨1,1,1,7859,7953,-286655947989,-280966239567⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7859 95 ⟨-286655929678,-280966257878⟩
  rw [← get_eq_raw]
  exact (append (widen s7859_1 (by decide)) (append (widen s7860_4 (by decide)) (append (widen s7864_8 (by decide)) (append (widen s7872_64 (by decide)) (append (widen s7936_16 (by decide)) (widen s7952_2 (by decide)))))))

theorem claim87 : CheckedClaim verifiedRow ⟨1,1,1,7859,7984,-286655947989,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7859 126 ⟨-286655929678,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7859_1 (by decide)) (append (widen s7860_4 (by decide)) (append (widen s7864_8 (by decide)) (append (widen s7872_64 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))

theorem claim88 : CheckedClaim verifiedRow ⟨1,1,1,7860,7984,-286595604855,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7860 125 ⟨-286595586544,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7860_4 (by decide)) (append (widen s7864_8 (by decide)) (append (widen s7872_64 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))

theorem claim89 : CheckedClaim verifiedRow ⟨1,1,1,7921,7968,-282906954802,-280055323004⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7921 48 ⟨-282906936491,-280055341315⟩
  rw [← get_eq_raw]
  exact (append (widen s7921_1 (by decide)) (append (widen s7922_2 (by decide)) (append (widen s7924_4 (by decide)) (append (widen s7928_8 (by decide)) (append (widen s7936_32 (by decide)) (widen s7968_1 (by decide)))))))

theorem claim90 : CheckedClaim verifiedRow ⟨1,1,1,7921,7984,-282906954802,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7921 64 ⟨-282906936491,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7921_1 (by decide)) (append (widen s7922_2 (by decide)) (append (widen s7924_4 (by decide)) (append (widen s7928_8 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))

theorem claim91 : CheckedClaim verifiedRow ⟨1,1,1,7922,7984,-282846364533,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7922 63 ⟨-282846346222,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7922_2 (by decide)) (append (widen s7924_4 (by decide)) (append (widen s7928_8 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))

theorem claim92 : CheckedClaim verifiedRow ⟨1,1,1,7922,8046,-282846364533,-275307317541⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7922 125 ⟨-282846346222,-275307335852⟩
  rw [← get_eq_raw]
  exact (append (widen s7922_2 (by decide)) (append (widen s7924_4 (by decide)) (append (widen s7928_8 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_8 (by decide)) (append (widen s8040_4 (by decide)) (append (widen s8044_2 (by decide)) (widen s8046_1 (by decide))))))))))

theorem claim93 : CheckedClaim verifiedRow ⟨1,1,1,7952,7984,-281026976939,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7952 33 ⟨-281026958628,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7952_16 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))

theorem claim94 : CheckedClaim verifiedRow ⟨1,1,1,7952,8000,-281026976939,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7952 49 ⟨-281026958628,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7952_16 (by decide)) (append (widen s7968_32 (by decide)) (widen s8000_1 (by decide))))

theorem claim95 : CheckedClaim verifiedRow ⟨1,1,1,7953,7984,-280966276192,-279082864610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7953 32 ⟨-280966257881,-279082882921⟩
  rw [← get_eq_raw]
  exact (append (widen s7953_1 (by decide)) (append (widen s7954_2 (by decide)) (append (widen s7956_4 (by decide)) (append (widen s7960_8 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))

theorem claim96 : CheckedClaim verifiedRow ⟨1,1,1,7953,8000,-280966276192,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7953 48 ⟨-280966257881,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7953_1 (by decide)) (append (widen s7954_2 (by decide)) (append (widen s7956_4 (by decide)) (append (widen s7960_8 (by decide)) (append (widen s7968_32 (by decide)) (widen s8000_1 (by decide)))))))

theorem claim97 : CheckedClaim verifiedRow ⟨1,1,1,7953,8015,-280966276192,-277196469295⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7953 63 ⟨-280966257881,-277196487606⟩
  rw [← get_eq_raw]
  exact (append (widen s7953_1 (by decide)) (append (widen s7954_2 (by decide)) (append (widen s7956_4 (by decide)) (append (widen s7960_8 (by decide)) (append (widen s7968_32 (by decide)) (widen s8000_16 (by decide)))))))

theorem claim98 : CheckedClaim verifiedRow ⟨1,1,1,7968,7992,-280055359629,-278596331429⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7968 25 ⟨-280055341318,-278596349740⟩
  rw [← get_eq_raw]
  exact (append (widen s7968_16 (by decide)) (append (widen s7984_8 (by decide)) (widen s7992_1 (by decide))))

theorem claim99 : CheckedClaim verifiedRow ⟨1,1,1,7968,8000,-280055359629,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7968 33 ⟨-280055341318,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7968_32 (by decide)) (widen s8000_1 (by decide)))

theorem claim100 : CheckedClaim verifiedRow ⟨1,1,1,7969,7992,-279994605241,-278596331429⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7969 24 ⟨-279994586930,-278596349740⟩
  rw [← get_eq_raw]
  exact (append (widen s7969_1 (by decide)) (append (widen s7970_2 (by decide)) (append (widen s7972_4 (by decide)) (append (widen s7976_8 (by decide)) (append (widen s7984_8 (by decide)) (widen s7992_1 (by decide)))))))

theorem claim101 : CheckedClaim verifiedRow ⟨1,1,1,7969,7999,-279994605241,-278170453480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7969 31 ⟨-279994586930,-278170471791⟩
  rw [← get_eq_raw]
  exact (append (widen s7969_1 (by decide)) (append (widen s7970_2 (by decide)) (append (widen s7972_4 (by decide)) (append (widen s7976_8 (by decide)) (widen s7984_16 (by decide))))))

theorem claim102 : CheckedClaim verifiedRow ⟨1,1,1,7976,7992,-279569233281,-278596331429⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7976 17 ⟨-279569214970,-278596349740⟩
  rw [← get_eq_raw]
  exact (append (widen s7976_8 (by decide)) (append (widen s7984_8 (by decide)) (widen s7992_1 (by decide))))

theorem claim103 : CheckedClaim verifiedRow ⟨1,1,1,7984,7995,-279082901235,-278413830560⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 12 ⟨-279082882924,-278413848871⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_8 (by decide)) (widen s7992_4 (by decide)))

theorem claim104 : CheckedClaim verifiedRow ⟨1,1,1,7984,7996,-279082901235,-278352990836⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 13 ⟨-279082882924,-278353009147⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_8 (by decide)) (append (widen s7992_4 (by decide)) (widen s7996_1 (by decide))))

theorem claim105 : CheckedClaim verifiedRow ⟨1,1,1,7984,7999,-279082901235,-278170453480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 16 ⟨-279082882924,-278170471791⟩
  rw [← get_eq_raw]
  exact (widen s7984_16 (by decide))

theorem claim106 : CheckedClaim verifiedRow ⟨1,1,1,7984,8000,-279082901235,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 17 ⟨-279082882924,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (widen s8000_1 (by decide)))

theorem claim107 : CheckedClaim verifiedRow ⟨1,1,1,7984,8108,-279082901235,-271521788552⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 125 ⟨-279082882924,-271521806863⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_8 (by decide)) (append (widen s8104_4 (by decide)) (widen s8108_1 (by decide)))))))

theorem claim108 : CheckedClaim verifiedRow ⟨1,1,1,7984,8109,-279082901235,-271460661252⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 126 ⟨-279082882924,-271460679563⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_8 (by decide)) (append (widen s8104_4 (by decide)) (widen s8108_2 (by decide)))))))

theorem claim109 : CheckedClaim verifiedRow ⟨1,1,1,7984,8232,-279082901235,-263928999887⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 249 ⟨-279082882924,-263929018198⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_32 (by decide)) (append (widen s8224_8 (by decide)) (widen s8232_1 (by decide)))))))

theorem claim110 : CheckedClaim verifiedRow ⟨1,1,1,7984,8233,-279082901235,-263867682872⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 250 ⟨-279082882924,-263867701183⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_32 (by decide)) (append (widen s8224_8 (by decide)) (widen s8232_2 (by decide)))))))

theorem claim111 : CheckedClaim verifiedRow ⟨1,1,1,7984,8481,-279082901235,-248650445016⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 498 ⟨-279082882924,-248650463327⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_256 (by decide)) (append (widen s8448_32 (by decide)) (widen s8480_2 (by decide)))))))

theorem claim112 : CheckedClaim verifiedRow ⟨1,1,1,7984,8978,-279082901235,-218437440449⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 995 ⟨-279082882924,-218437458760⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_512 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_16 (by decide)) (append (widen s8976_2 (by decide)) (widen s8978_1 (by decide)))))))))

theorem claim113 : CheckedClaim verifiedRow ⟨1,1,1,7984,9972,-279082901235,-161810581645⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 1989 ⟨-279082882924,-161810599956⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide))))))))))))

theorem claim114 : CheckedClaim verifiedRow ⟨1,1,1,7984,10966,-279082901235,-113632117338⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 2983 ⟨-279082882924,-113632135649⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_128 (by decide)) (append (widen s10880_64 (by decide)) (append (widen s10944_16 (by decide)) (append (widen s10960_4 (by decide)) (append (widen s10964_2 (by decide)) (widen s10966_1 (by decide))))))))))))

theorem claim115 : CheckedClaim verifiedRow ⟨1,1,1,7984,11960,-279082901235,-75605548635⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7984 3977 ⟨-279082882924,-75605566946⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide))))))))))))

theorem claim116 : CheckedClaim verifiedRow ⟨1,1,1,7988,7996,-278839659502,-278352990836⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7988 9 ⟨-278839641191,-278353009147⟩
  rw [← get_eq_raw]
  exact (append (widen s7988_4 (by decide)) (append (widen s7992_4 (by decide)) (widen s7996_1 (by decide))))

theorem claim117 : CheckedClaim verifiedRow ⟨1,1,1,7988,7999,-278839659502,-278170453480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7988 12 ⟨-278839641191,-278170471791⟩
  rw [← get_eq_raw]
  exact (append (widen s7988_4 (by decide)) (widen s7992_8 (by decide)))

theorem claim118 : CheckedClaim verifiedRow ⟨1,1,1,7992,7996,-278596368054,-278352990836⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7992 5 ⟨-278596349743,-278353009147⟩
  rw [← get_eq_raw]
  exact (append (widen s7992_4 (by decide)) (widen s7996_1 (by decide)))

theorem claim119 : CheckedClaim verifiedRow ⟨1,1,1,7992,7998,-278596368054,-278231302286⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7992 7 ⟨-278596349743,-278231320597⟩
  rw [← get_eq_raw]
  exact (append (widen s7992_4 (by decide)) (append (widen s7996_2 (by decide)) (widen s7998_1 (by decide))))

theorem claim120 : CheckedClaim verifiedRow ⟨1,1,1,7992,7999,-278596368054,-278170453480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7992 8 ⟨-278596349743,-278170471791⟩
  rw [← get_eq_raw]
  exact (widen s7992_8 (by decide))

theorem claim121 : CheckedClaim verifiedRow ⟨1,1,1,7992,8000,-278596368054,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7992 9 ⟨-278596349743,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7992_8 (by decide)) (widen s8000_1 (by decide)))

theorem claim122 : CheckedClaim verifiedRow ⟨1,1,1,7994,7998,-278474703865,-278231302286⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7994 5 ⟨-278474685554,-278231320597⟩
  rw [← get_eq_raw]
  exact (append (widen s7994_2 (by decide)) (append (widen s7996_2 (by decide)) (widen s7998_1 (by decide))))

theorem claim123 : CheckedClaim verifiedRow ⟨1,1,1,7994,8000,-278474703865,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7994 7 ⟨-278474685554,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7994_2 (by decide)) (append (widen s7996_4 (by decide)) (widen s8000_1 (by decide))))

theorem claim124 : CheckedClaim verifiedRow ⟨1,1,1,7996,7999,-278353027461,-278170453480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7996 4 ⟨-278353009150,-278170471791⟩
  rw [← get_eq_raw]
  exact (widen s7996_4 (by decide))

theorem claim125 : CheckedClaim verifiedRow ⟨1,1,1,7996,8000,-278353027461,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7996 5 ⟨-278353009150,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7996_4 (by decide)) (widen s8000_1 (by decide)))

theorem claim126 : CheckedClaim verifiedRow ⟨1,1,1,7996,8004,-278353027461,-277866164481⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7996 9 ⟨-278353009150,-277866182792⟩
  rw [← get_eq_raw]
  exact (append (widen s7996_4 (by decide)) (append (widen s8000_4 (by decide)) (widen s8004_1 (by decide))))

theorem claim127 : CheckedClaim verifiedRow ⟨1,1,1,7997,7999,-278292184700,-278170453480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7997 3 ⟨-278292166389,-278170471791⟩
  rw [← get_eq_raw]
  exact (append (widen s7997_1 (by decide)) (widen s7998_2 (by decide)))

theorem claim128 : CheckedClaim verifiedRow ⟨1,1,1,7997,8000,-278292184700,-278109601664⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7997 4 ⟨-278292166389,-278109619975⟩
  rw [← get_eq_raw]
  exact (append (widen s7997_1 (by decide)) (append (widen s7998_2 (by decide)) (widen s8000_1 (by decide))))

theorem claim129 : CheckedClaim verifiedRow ⟨1,1,1,7998,8002,-278231338911,-277987889038⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7998 5 ⟨-278231320600,-277987907349⟩
  rw [← get_eq_raw]
  exact (append (widen s7998_2 (by decide)) (append (widen s8000_2 (by decide)) (widen s8002_1 (by decide))))

theorem claim130 : CheckedClaim verifiedRow ⟨1,1,1,7999,8015,-278170490105,-277196469295⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7999 17 ⟨-278170471794,-277196487606⟩
  rw [← get_eq_raw]
  exact (append (widen s7999_1 (by decide)) (widen s8000_16 (by decide)))

theorem claim131 : CheckedClaim verifiedRow ⟨1,1,1,7999,8031,-278170490105,-276221750863⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 7999 33 ⟨-278170471794,-276221769174⟩
  rw [← get_eq_raw]
  exact (append (widen s7999_1 (by decide)) (widen s8000_32 (by decide)))

theorem claim132 : CheckedClaim verifiedRow ⟨1,1,1,8000,8002,-278109638289,-277987889038⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 3 ⟨-278109619978,-277987907349⟩
  rw [← get_eq_raw]
  exact (append (widen s8000_2 (by decide)) (widen s8002_1 (by decide)))

theorem claim133 : CheckedClaim verifiedRow ⟨1,1,1,8000,8003,-278109638289,-277927028246⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 4 ⟨-278109619978,-277927046557⟩
  rw [← get_eq_raw]
  exact (widen s8000_4 (by decide))

theorem claim134 : CheckedClaim verifiedRow ⟨1,1,1,8000,8004,-278109638289,-277866164481⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 5 ⟨-278109619978,-277866182792⟩
  rw [← get_eq_raw]
  exact (append (widen s8000_4 (by decide)) (widen s8004_1 (by decide)))

theorem claim135 : CheckedClaim verifiedRow ⟨1,1,1,8000,8007,-278109638289,-277683555427⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 8 ⟨-278109619978,-277683573738⟩
  rw [← get_eq_raw]
  exact (widen s8000_8 (by decide))

theorem claim136 : CheckedClaim verifiedRow ⟨1,1,1,8000,8008,-278109638289,-277622679853⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 9 ⟨-278109619978,-277622698164⟩
  rw [← get_eq_raw]
  exact (append (widen s8000_8 (by decide)) (widen s8008_1 (by decide)))

theorem claim137 : CheckedClaim verifiedRow ⟨1,1,1,8000,8015,-278109638289,-277196469295⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 16 ⟨-278109619978,-277196487606⟩
  rw [← get_eq_raw]
  exact (widen s8000_16 (by decide))

theorem claim138 : CheckedClaim verifiedRow ⟨1,1,1,8000,8016,-278109638289,-277135570529⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 17 ⟨-278109619978,-277135588840⟩
  rw [← get_eq_raw]
  exact (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))

theorem claim139 : CheckedClaim verifiedRow ⟨1,1,1,8000,8031,-278109638289,-276221750863⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 32 ⟨-278109619978,-276221769174⟩
  rw [← get_eq_raw]
  exact (widen s8000_32 (by decide))

theorem claim140 : CheckedClaim verifiedRow ⟨1,1,1,8000,8046,-278109638289,-275307317541⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 47 ⟨-278109619978,-275307335852⟩
  rw [← get_eq_raw]
  exact (append (widen s8000_32 (by decide)) (append (widen s8032_8 (by decide)) (append (widen s8040_4 (by decide)) (append (widen s8044_2 (by decide)) (widen s8046_1 (by decide))))))

theorem claim141 : CheckedClaim verifiedRow ⟨1,1,1,8000,8047,-278109638289,-275246334225⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8000 48 ⟨-278109619978,-275246352536⟩
  rw [← get_eq_raw]
  exact (append (widen s8000_32 (by decide)) (widen s8032_16 (by decide)))

theorem claim142 : CheckedClaim verifiedRow ⟨1,1,1,8001,8003,-278048783472,-277927028246⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8001 3 ⟨-278048765161,-277927046557⟩
  rw [← get_eq_raw]
  exact (append (widen s8001_1 (by decide)) (widen s8002_2 (by decide)))

theorem claim143 : CheckedClaim verifiedRow ⟨1,1,1,8001,8005,-278048783472,-277805297750⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8001 5 ⟨-278048765161,-277805316061⟩
  rw [← get_eq_raw]
  exact (append (widen s8001_1 (by decide)) (append (widen s8002_2 (by decide)) (widen s8004_2 (by decide))))

theorem claim144 : CheckedClaim verifiedRow ⟨1,1,1,8001,8007,-278048783472,-277683555427⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8001 7 ⟨-278048765161,-277683573738⟩
  rw [← get_eq_raw]
  exact (append (widen s8001_1 (by decide)) (append (widen s8002_2 (by decide)) (widen s8004_4 (by decide))))

theorem claim145 : CheckedClaim verifiedRow ⟨1,1,1,8002,8007,-277987925663,-277683555427⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8002 6 ⟨-277987907352,-277683573738⟩
  rw [← get_eq_raw]
  exact (append (widen s8002_2 (by decide)) (widen s8004_4 (by decide)))

theorem claim146 : CheckedClaim verifiedRow ⟨1,1,1,8003,8007,-277927064871,-277683555427⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8003 5 ⟨-277927046560,-277683573738⟩
  rw [← get_eq_raw]
  exact (append (widen s8003_1 (by decide)) (widen s8004_4 (by decide)))

theorem claim147 : CheckedClaim verifiedRow ⟨1,1,1,8003,8011,-277927064871,-277440035588⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8003 9 ⟨-277927046560,-277440053899⟩
  rw [← get_eq_raw]
  exact (append (widen s8003_1 (by decide)) (append (widen s8004_4 (by decide)) (widen s8008_4 (by decide))))

theorem claim148 : CheckedClaim verifiedRow ⟨1,1,1,8003,8015,-277927064871,-277196469295⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8003 13 ⟨-277927046560,-277196487606⟩
  rw [← get_eq_raw]
  exact (append (widen s8003_1 (by decide)) (append (widen s8004_4 (by decide)) (widen s8008_8 (by decide))))

theorem claim149 : CheckedClaim verifiedRow ⟨1,1,1,8004,8015,-277866201106,-277196469295⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8004 12 ⟨-277866182795,-277196487606⟩
  rw [← get_eq_raw]
  exact (append (widen s8004_4 (by decide)) (widen s8008_8 (by decide)))

theorem claim150 : CheckedClaim verifiedRow ⟨1,1,1,8007,8015,-277683592052,-277196469295⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8007 9 ⟨-277683573741,-277196487606⟩
  rw [← get_eq_raw]
  exact (append (widen s8007_1 (by decide)) (widen s8008_8 (by decide)))

theorem claim151 : CheckedClaim verifiedRow ⟨1,1,1,8007,8023,-277683592052,-276709199603⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8007 17 ⟨-277683573741,-276709217914⟩
  rw [← get_eq_raw]
  exact (append (widen s8007_1 (by decide)) (append (widen s8008_8 (by decide)) (widen s8016_8 (by decide))))

theorem claim152 : CheckedClaim verifiedRow ⟨1,1,1,8007,8031,-277683592052,-276221750863⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8007 25 ⟨-277683573741,-276221769174⟩
  rw [← get_eq_raw]
  exact (append (widen s8007_1 (by decide)) (append (widen s8008_8 (by decide)) (widen s8016_16 (by decide))))

theorem claim153 : CheckedClaim verifiedRow ⟨1,1,1,8008,8031,-277622716478,-276221750863⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8008 24 ⟨-277622698167,-276221769174⟩
  rw [← get_eq_raw]
  exact (append (widen s8008_8 (by decide)) (widen s8016_16 (by decide)))

theorem claim154 : CheckedClaim verifiedRow ⟨1,1,1,8015,8047,-277196505920,-275246334225⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8015 33 ⟨-277196487609,-275246352536⟩
  rw [← get_eq_raw]
  exact (append (widen s8015_1 (by decide)) (append (widen s8016_16 (by decide)) (widen s8032_16 (by decide))))

theorem claim155 : CheckedClaim verifiedRow ⟨1,1,1,8015,8078,-277196505920,-273354611438⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8015 64 ⟨-277196487609,-273354629749⟩
  rw [← get_eq_raw]
  exact (append (widen s8015_1 (by decide)) (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_8 (by decide)) (append (widen s8072_4 (by decide)) (append (widen s8076_2 (by decide)) (widen s8078_1 (by decide))))))))

theorem claim156 : CheckedClaim verifiedRow ⟨1,1,1,8015,8108,-277196505920,-271521788552⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8015 94 ⟨-277196487609,-271521806863⟩
  rw [← get_eq_raw]
  exact (append (widen s8015_1 (by decide)) (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_8 (by decide)) (append (widen s8104_4 (by decide)) (widen s8108_1 (by decide))))))))

theorem claim157 : CheckedClaim verifiedRow ⟨1,1,1,8016,8078,-277135607154,-273354611438⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8016 63 ⟨-277135588843,-273354629749⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_8 (by decide)) (append (widen s8072_4 (by decide)) (append (widen s8076_2 (by decide)) (widen s8078_1 (by decide)))))))

theorem claim158 : CheckedClaim verifiedRow ⟨1,1,1,8016,8109,-277135607154,-271460661252⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8016 94 ⟨-277135588843,-271460679563⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_8 (by decide)) (append (widen s8104_4 (by decide)) (widen s8108_2 (by decide)))))))

theorem claim159 : CheckedClaim verifiedRow ⟨1,1,1,8016,10004,-277135607154,-160112141240⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8016 1989 ⟨-277135588843,-160112159551⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide))))))))))

theorem claim160 : CheckedClaim verifiedRow ⟨1,1,1,8016,10998,-277135607154,-112247170376⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8016 2983 ⟨-277135588843,-112247188687⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_128 (by decide)) (append (widen s10880_64 (by decide)) (append (widen s10944_32 (by decide)) (append (widen s10976_16 (by decide)) (append (widen s10992_4 (by decide)) (append (widen s10996_2 (by decide)) (widen s10998_1 (by decide)))))))))))))

theorem claim161 : CheckedClaim verifiedRow ⟨1,1,1,8016,11992,-277135607154,-74550015650⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8016 3977 ⟨-277135588843,-74550033961⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))

private theorem s11776_512 : Run get 11776 512 ⟨-81874539065,-65293010688⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨-101150478019,-65293010688⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨-147872883356,-65293010688⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨-266380777358,-65293010688⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨-65263060242,-51160951863⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨-51135623755,-39257042091⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨-65263060242,-39257042091⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨-39235777331,-29272467526⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

theorem claim162 : CheckedClaim verifiedRow ⟨1,1,1,8016,13980,-277135607154,-26543188517⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8016 5965 ⟨-277135588843,-26543206828⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide))))))))))))

theorem claim163 : CheckedClaim verifiedRow ⟨1,1,1,8031,8078,-276221787488,-273354611438⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8031 48 ⟨-276221769177,-273354629749⟩
  rw [← get_eq_raw]
  exact (append (widen s8031_1 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_8 (by decide)) (append (widen s8072_4 (by decide)) (append (widen s8076_2 (by decide)) (widen s8078_1 (by decide)))))))

theorem claim164 : CheckedClaim verifiedRow ⟨1,1,1,8046,8171,-275307354166,-267667102885⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8046 126 ⟨-275307335855,-267667121196⟩
  rw [← get_eq_raw]
  exact (append (widen s8046_2 (by decide)) (append (widen s8048_16 (by decide)) (append (widen s8064_64 (by decide)) (append (widen s8128_32 (by decide)) (append (widen s8160_8 (by decide)) (widen s8168_4 (by decide)))))))

theorem claim165 : CheckedClaim verifiedRow ⟨1,1,1,8046,8232,-275307354166,-263928999887⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8046 187 ⟨-275307335855,-263929018198⟩
  rw [← get_eq_raw]
  exact (append (widen s8046_2 (by decide)) (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_32 (by decide)) (append (widen s8224_8 (by decide)) (widen s8232_1 (by decide)))))))

theorem claim166 : CheckedClaim verifiedRow ⟨1,1,1,8047,8109,-275246370850,-271460661252⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8047 63 ⟨-275246352539,-271460679563⟩
  rw [← get_eq_raw]
  exact (append (widen s8047_1 (by decide)) (append (widen s8048_16 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_8 (by decide)) (append (widen s8104_4 (by decide)) (widen s8108_2 (by decide)))))))

theorem claim167 : CheckedClaim verifiedRow ⟨1,1,1,8047,8171,-275246370850,-267667102885⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8047 125 ⟨-275246352539,-267667121196⟩
  rw [← get_eq_raw]
  exact (append (widen s8047_1 (by decide)) (append (widen s8048_16 (by decide)) (append (widen s8064_64 (by decide)) (append (widen s8128_32 (by decide)) (append (widen s8160_8 (by decide)) (widen s8168_4 (by decide)))))))

theorem claim168 : CheckedClaim verifiedRow ⟨1,1,1,8047,8233,-275246370850,-263867682872⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8047 187 ⟨-275246352539,-263867701183⟩
  rw [← get_eq_raw]
  exact (append (widen s8047_1 (by decide)) (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_32 (by decide)) (append (widen s8224_8 (by decide)) (widen s8232_2 (by decide)))))))

theorem claim169 : CheckedClaim verifiedRow ⟨1,1,1,8048,10036,-275185384947,-158422794072⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8048 1989 ⟨-275185366636,-158422812383⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))

theorem claim170 : CheckedClaim verifiedRow ⟨1,1,1,8048,11030,-275185384947,-110872941610⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8048 2983 ⟨-275185366636,-110872959921⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_256 (by decide)) (append (widen s11008_16 (by decide)) (append (widen s11024_4 (by decide)) (append (widen s11028_2 (by decide)) (widen s11030_1 (by decide))))))))))

theorem claim171 : CheckedClaim verifiedRow ⟨1,1,1,8048,12024,-275185384947,-73504665661⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8048 3977 ⟨-275185366636,-73504683972⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))

theorem claim172 : CheckedClaim verifiedRow ⟨1,1,1,8048,14012,-275185384947,-26004189785⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8048 5965 ⟨-275185366636,-26004208096⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide))))))))))))

theorem claim173 : CheckedClaim verifiedRow ⟨1,1,1,8080,12056,-273232522183,-72469454810⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8080 3977 ⟨-273232503872,-72469473121⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

theorem claim174 : CheckedClaim verifiedRow ⟨1,1,1,8108,8356,-271521825177,-256320532099⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8108 249 ⟨-271521806866,-256320550410⟩
  rw [← get_eq_raw]
  exact (append (widen s8108_4 (by decide)) (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_128 (by decide)) (append (widen s8320_32 (by decide)) (append (widen s8352_4 (by decide)) (widen s8356_1 (by decide))))))))

theorem claim175 : CheckedClaim verifiedRow ⟨1,1,1,8108,8357,-271521825177,-256259152055⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8108 250 ⟨-271521806866,-256259170366⟩
  rw [← get_eq_raw]
  exact (append (widen s8108_4 (by decide)) (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_128 (by decide)) (append (widen s8320_32 (by decide)) (append (widen s8352_4 (by decide)) (widen s8356_2 (by decide))))))))

theorem claim176 : CheckedClaim verifiedRow ⟨1,1,1,8108,8481,-271521825177,-248650445016⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8108 374 ⟨-271521806866,-248650463327⟩
  rw [← get_eq_raw]
  exact (append (widen s8108_4 (by decide)) (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_256 (by decide)) (append (widen s8448_32 (by decide)) (widen s8480_2 (by decide)))))))

theorem claim177 : CheckedClaim verifiedRow ⟨1,1,1,8109,8233,-271460697877,-263867682872⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8109 125 ⟨-271460679566,-263867701183⟩
  rw [← get_eq_raw]
  exact (append (widen s8109_1 (by decide)) (append (widen s8110_2 (by decide)) (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_32 (by decide)) (append (widen s8224_8 (by decide)) (widen s8232_2 (by decide))))))))

theorem claim178 : CheckedClaim verifiedRow ⟨1,1,1,8109,8481,-271460697877,-248650445016⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8109 373 ⟨-271460679566,-248650463327⟩
  rw [← get_eq_raw]
  exact (append (widen s8109_1 (by decide)) (append (widen s8110_2 (by decide)) (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_256 (by decide)) (append (widen s8448_32 (by decide)) (widen s8480_2 (by decide))))))))

theorem claim179 : CheckedClaim verifiedRow ⟨1,1,1,8112,12088,-271277303708,-71444337883⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8112 3977 ⟨-271277285397,-71444356194⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_32 (by decide)) (append (widen s12064_16 (by decide)) (append (widen s12080_8 (by decide)) (widen s12088_1 (by decide)))))))))))

theorem claim180 : CheckedClaim verifiedRow ⟨1,1,1,8232,8730,-263929036512,-233429757762⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8232 499 ⟨-263929018201,-233429776073⟩
  rw [← get_eq_raw]
  exact (append (widen s8232_8 (by decide)) (append (widen s8240_16 (by decide)) (append (widen s8256_64 (by decide)) (append (widen s8320_128 (by decide)) (append (widen s8448_256 (by decide)) (append (widen s8704_16 (by decide)) (append (widen s8720_8 (by decide)) (append (widen s8728_2 (by decide)) (widen s8730_1 (by decide))))))))))

theorem claim181 : CheckedClaim verifiedRow ⟨1,1,1,8233,8978,-263867719497,-218437440449⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8233 746 ⟨-263867701186,-218437458760⟩
  rw [← get_eq_raw]
  exact (append (widen s8233_1 (by decide)) (append (widen s8234_2 (by decide)) (append (widen s8236_4 (by decide)) (append (widen s8240_16 (by decide)) (append (widen s8256_64 (by decide)) (append (widen s8320_128 (by decide)) (append (widen s8448_256 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_16 (by decide)) (append (widen s8976_2 (by decide)) (widen s8978_1 (by decide))))))))))))

theorem claim182 : CheckedClaim verifiedRow ⟨1,1,1,8481,9475,-248650481641,-189275870043⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8481 995 ⟨-248650463330,-189275888354⟩
  rw [← get_eq_raw]
  exact (append (widen s8481_1 (by decide)) (append (widen s8482_2 (by decide)) (append (widen s8484_4 (by decide)) (append (widen s8488_8 (by decide)) (append (widen s8496_16 (by decide)) (append (widen s8512_64 (by decide)) (append (widen s8576_128 (by decide)) (append (widen s8704_512 (by decide)) (append (widen s9216_256 (by decide)) (widen s9472_4 (by decide)))))))))))

theorem claim183 : CheckedClaim verifiedRow ⟨1,1,1,8481,9972,-248650481641,-161810581645⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8481 1492 ⟨-248650463330,-161810599956⟩
  rw [← get_eq_raw]
  exact (append (widen s8481_1 (by decide)) (append (widen s8482_2 (by decide)) (append (widen s8484_4 (by decide)) (append (widen s8488_8 (by decide)) (append (widen s8496_16 (by decide)) (append (widen s8512_64 (by decide)) (append (widen s8576_128 (by decide)) (append (widen s8704_512 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide))))))))))))))))

theorem claim184 : CheckedClaim verifiedRow ⟨1,1,1,8978,10966,-218437477074,-113632117338⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8978 1989 ⟨-218437458763,-113632135649⟩
  rw [← get_eq_raw]
  exact (append (widen s8978_2 (by decide)) (append (widen s8980_4 (by decide)) (append (widen s8984_8 (by decide)) (append (widen s8992_32 (by decide)) (append (widen s9024_64 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_128 (by decide)) (append (widen s10880_64 (by decide)) (append (widen s10944_16 (by decide)) (append (widen s10960_4 (by decide)) (append (widen s10964_2 (by decide)) (widen s10966_1 (by decide)))))))))))))))

theorem claim185 : CheckedClaim verifiedRow ⟨1,1,1,8978,11960,-218437477074,-75605548635⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 8978 2983 ⟨-218437458763,-75605566946⟩
  rw [← get_eq_raw]
  exact (append (widen s8978_2 (by decide)) (append (widen s8980_4 (by decide)) (append (widen s8984_8 (by decide)) (append (widen s8992_32 (by decide)) (append (widen s9024_64 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide)))))))))))))))

theorem claim186 : CheckedClaim verifiedRow ⟨1,1,1,9010,10998,-216520333843,-112247170376⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 9010 1989 ⟨-216520315532,-112247188687⟩
  rw [← get_eq_raw]
  exact (append (widen s9010_2 (by decide)) (append (widen s9012_4 (by decide)) (append (widen s9016_8 (by decide)) (append (widen s9024_64 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_128 (by decide)) (append (widen s10880_64 (by decide)) (append (widen s10944_32 (by decide)) (append (widen s10976_16 (by decide)) (append (widen s10992_4 (by decide)) (append (widen s10996_2 (by decide)) (widen s10998_1 (by decide)))))))))))))))

theorem claim187 : CheckedClaim verifiedRow ⟨1,1,1,9010,11992,-216520333843,-74550015650⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 9010 2983 ⟨-216520315532,-74550033961⟩
  rw [← get_eq_raw]
  exact (append (widen s9010_2 (by decide)) (append (widen s9012_4 (by decide)) (append (widen s9016_8 (by decide)) (append (widen s9024_64 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))))

theorem claim188 : CheckedClaim verifiedRow ⟨1,1,1,9042,12024,-214607810142,-73504665661⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 9042 2983 ⟨-214607791831,-73504683972⟩
  rw [← get_eq_raw]
  exact (append (widen s9042_2 (by decide)) (append (widen s9044_4 (by decide)) (append (widen s9048_8 (by decide)) (append (widen s9056_32 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))))

theorem claim189 : CheckedClaim verifiedRow ⟨1,1,1,9972,11960,-161810618270,-75605548635⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 9972 1989 ⟨-161810599959,-75605566946⟩
  rw [← get_eq_raw]
  exact (append (widen s9972_4 (by decide)) (append (widen s9976_8 (by decide)) (append (widen s9984_256 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide)))))))))))

theorem claim190 : CheckedClaim verifiedRow ⟨1,1,1,9972,12954,-161810618270,-47335368171⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 9972 2983 ⟨-161810599959,-47335386482⟩
  rw [← get_eq_raw]
  exact (append (widen s9972_4 (by decide)) (append (widen s9976_8 (by decide)) (append (widen s9984_256 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_16 (by decide)) (append (widen s12944_8 (by decide)) (append (widen s12952_2 (by decide)) (widen s12954_1 (by decide)))))))))))

theorem claim191 : CheckedClaim verifiedRow ⟨1,1,1,9972,13948,-161810618270,-27087925936⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 9972 3977 ⟨-161810599959,-27087944247⟩
  rw [← get_eq_raw]
  exact (append (widen s9972_4 (by decide)) (append (widen s9976_8 (by decide)) (append (widen s9984_256 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_64 (by decide)) (append (widen s13888_32 (by decide)) (append (widen s13920_16 (by decide)) (append (widen s13936_8 (by decide)) (append (widen s13944_4 (by decide)) (widen s13948_1 (by decide)))))))))))))

private theorem s13824_512 : Run get 13824 512 ⟨-29254624869,-20865035953⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨-39235777331,-20865035953⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨-65263060242,-20865035953⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨-20849924494,-13673441248⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨-13660343599,-7326894127⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨-20849924494,-7326894127⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨-7315081065,-1450784265⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim192 : CheckedClaim verifiedRow ⟨1,1,1,9972,15936,-161810618270,-719375833⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 9972 5965 ⟨-161810599959,-719394144⟩
  rw [← get_eq_raw]
  exact (append (widen s9972_4 (by decide)) (append (widen s9976_8 (by decide)) (append (widen s9984_256 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide))))))))))

theorem claim193 : CheckedClaim verifiedRow ⟨1,1,1,10004,11992,-160112177865,-74550015650⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10004 1989 ⟨-160112159554,-74550033961⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide)))))))))))))

theorem claim194 : CheckedClaim verifiedRow ⟨1,1,1,10004,12986,-160112177865,-46570306846⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10004 2983 ⟨-160112159554,-46570325157⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_32 (by decide)) (append (widen s12960_16 (by decide)) (append (widen s12976_8 (by decide)) (append (widen s12984_2 (by decide)) (widen s12986_1 (by decide))))))))))))))

theorem claim195 : CheckedClaim verifiedRow ⟨1,1,1,10004,13980,-160112177865,-26543188517⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10004 3977 ⟨-160112159554,-26543206828⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide))))))))))))))

theorem claim196 : CheckedClaim verifiedRow ⟨1,1,1,10004,15968,-160112177865,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10004 5965 ⟨-160112159554,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))))

theorem claim197 : CheckedClaim verifiedRow ⟨1,1,1,10036,12024,-158422830697,-73504665661⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10036 1989 ⟨-158422812386,-73504683972⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim198 : CheckedClaim verifiedRow ⟨1,1,1,10036,14012,-158422830697,-26004189785⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10036 3977 ⟨-158422812386,-26004208096⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide))))))))))))))

theorem claim199 : CheckedClaim verifiedRow ⟨1,1,1,10036,16000,-158422830697,18313⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10036 5965 ⟨-158422812386,2⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide)))))))))))

theorem claim200 : CheckedClaim verifiedRow ⟨1,1,1,10068,12056,-156742670599,-72469454810⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10068 1989 ⟨-156742652288,-72469473121⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

theorem claim201 : CheckedClaim verifiedRow ⟨1,1,1,10068,13050,-156742670599,-45065000052⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10068 2983 ⟨-156742652288,-45065018363⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_64 (by decide)) (append (widen s12992_32 (by decide)) (append (widen s13024_16 (by decide)) (append (widen s13040_8 (by decide)) (append (widen s13048_2 (by decide)) (widen s13050_1 (by decide))))))))))))))

theorem claim202 : CheckedClaim verifiedRow ⟨1,1,1,10068,16032,-156742670599,359669496⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10068 5965 ⟨-156742652288,359651185⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))))))

theorem claim203 : CheckedClaim verifiedRow ⟨1,1,1,10100,12088,-155071788427,-71444337883⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10100 1989 ⟨-155071770116,-71444356194⟩
  rw [← get_eq_raw]
  exact (append (widen s10100_4 (by decide)) (append (widen s10104_8 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_32 (by decide)) (append (widen s12064_16 (by decide)) (append (widen s12080_8 (by decide)) (widen s12088_1 (by decide)))))))))))

theorem claim204 : CheckedClaim verifiedRow ⟨1,1,1,10966,12954,-113632153963,-47335368171⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10966 1989 ⟨-113632135652,-47335386482⟩
  rw [← get_eq_raw]
  exact (append (widen s10966_2 (by decide)) (append (widen s10968_8 (by decide)) (append (widen s10976_32 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_16 (by decide)) (append (widen s12944_8 (by decide)) (append (widen s12952_2 (by decide)) (widen s12954_1 (by decide))))))))))))

theorem claim205 : CheckedClaim verifiedRow ⟨1,1,1,10966,13948,-113632153963,-27087925936⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10966 2983 ⟨-113632135652,-27087944247⟩
  rw [← get_eq_raw]
  exact (append (widen s10966_2 (by decide)) (append (widen s10968_8 (by decide)) (append (widen s10976_32 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_64 (by decide)) (append (widen s13888_32 (by decide)) (append (widen s13920_16 (by decide)) (append (widen s13936_8 (by decide)) (append (widen s13944_4 (by decide)) (widen s13948_1 (by decide))))))))))))))

theorem claim206 : CheckedClaim verifiedRow ⟨1,1,1,10998,11992,-112247207001,-74550015650⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10998 995 ⟨-112247188690,-74550033961⟩
  rw [← get_eq_raw]
  exact (append (widen s10998_2 (by decide)) (append (widen s11000_8 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))

theorem claim207 : CheckedClaim verifiedRow ⟨1,1,1,10998,12986,-112247207001,-46570306846⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10998 1989 ⟨-112247188690,-46570325157⟩
  rw [← get_eq_raw]
  exact (append (widen s10998_2 (by decide)) (append (widen s11000_8 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_32 (by decide)) (append (widen s12960_16 (by decide)) (append (widen s12976_8 (by decide)) (append (widen s12984_2 (by decide)) (widen s12986_1 (by decide))))))))))))

theorem claim208 : CheckedClaim verifiedRow ⟨1,1,1,10998,13980,-112247207001,-26543188517⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 10998 2983 ⟨-112247188690,-26543206828⟩
  rw [← get_eq_raw]
  exact (append (widen s10998_2 (by decide)) (append (widen s11000_8 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide))))))))))))

theorem claim209 : CheckedClaim verifiedRow ⟨1,1,1,11960,15936,-75605585260,-719375833⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11960 3977 ⟨-75605566949,-719394144⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide)))))))))

private theorem s15872_512 : Run get 15872 512 ⟨-1439522522,4330617821⟩ :=
  join s15872_256 s16128_256 (by decide) (by decide)

private theorem s15360_1024 : Run get 15360 1024 ⟨-7315081065,4330617821⟩ :=
  join s15360_512 s15872_512 (by decide) (by decide)

private theorem s14336_2048 : Run get 14336 2048 ⟨-20849924494,4330617821⟩ :=
  join s14336_1024 s15360_1024 (by decide) (by decide)

private theorem s12288_4096 : Run get 12288 4096 ⟨-65263060242,4330617821⟩ :=
  join s12288_2048 s14336_2048 (by decide) (by decide)

private theorem s16384_512 : Run get 16384 512 ⟨4342062397,10393178446⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨10405539771,17112270791⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨4342062397,17112270791⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨17126280746,24861104931⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

theorem claim210 : CheckedClaim verifiedRow ⟨1,1,1,11960,17924,-75605585260,24943092975⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11960 5965 ⟨-75605566949,24943074664⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_4 (by decide)) (widen s17924_1 (by decide)))))))))

private theorem s17920_512 : Run get 17920 512 ⟨24877488199,34006700548⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨17126280746,34006700548⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨4342062397,34006700548⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨34026163659,44902363284⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨44925575884,57875812557⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨34026163659,57875812557⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

theorem claim211 : CheckedClaim verifiedRow ⟨1,1,1,11960,19912,-75605585260,71444374508⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11960 7953 ⟨-75605566949,71444356197⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide))))))))))))

theorem claim212 : CheckedClaim verifiedRow ⟨1,1,1,11992,13483,-74550052275,-35705210558⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11992 1492 ⟨-74550033964,-35705228869⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_128 (by decide)) (append (widen s13440_32 (by decide)) (append (widen s13472_8 (by decide)) (widen s13480_4 (by decide)))))))))

theorem claim213 : CheckedClaim verifiedRow ⟨1,1,1,11992,13980,-74550052275,-26543188517⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11992 1989 ⟨-74550033964,-26543206828⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide)))))))))))

theorem claim214 : CheckedClaim verifiedRow ⟨1,1,1,11992,14974,-74550052275,-12034870943⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11992 2983 ⟨-74550033964,-12034889254⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_512 (by decide)) (append (widen s14848_64 (by decide)) (append (widen s14912_32 (by decide)) (append (widen s14944_16 (by decide)) (append (widen s14960_8 (by decide)) (append (widen s14968_4 (by decide)) (append (widen s14972_2 (by decide)) (widen s14974_1 (by decide)))))))))))))

theorem claim215 : CheckedClaim verifiedRow ⟨1,1,1,11992,15968,-74550052275,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11992 3977 ⟨-74550033964,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim216 : CheckedClaim verifiedRow ⟨1,1,1,11992,17956,-74550052275,25470878411⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 11992 5965 ⟨-74550033964,25470860100⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide))))))))))

theorem claim217 : CheckedClaim verifiedRow ⟨1,1,1,12024,14012,-73504702286,-26004189785⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12024 1989 ⟨-73504683975,-26004208096⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide)))))))))))

theorem claim218 : CheckedClaim verifiedRow ⟨1,1,1,12024,16000,-73504702286,18313⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12024 3977 ⟨-73504683975,2⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim219 : CheckedClaim verifiedRow ⟨1,1,1,12024,17988,-73504702286,26004226410⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12024 5965 ⟨-73504683975,26004208099⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide)))))))))

theorem claim220 : CheckedClaim verifiedRow ⟨1,1,1,12056,16032,-72469491435,359669496⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12056 3977 ⟨-72469473124,359651185⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim221 : CheckedClaim verifiedRow ⟨1,1,1,12056,18020,-72469491435,26543225142⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12056 5965 ⟨-72469473124,26543206831⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))))

theorem claim222 : CheckedClaim verifiedRow ⟨1,1,1,12088,16064,-71444374508,719412458⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12088 3977 ⟨-71444356197,719394147⟩
  rw [← get_eq_raw]
  exact (append (widen s12088_8 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim223 : CheckedClaim verifiedRow ⟨1,1,1,12986,13980,-46570343471,-26543188517⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12986 995 ⟨-46570325160,-26543206828⟩
  rw [← get_eq_raw]
  exact (append (widen s12986_2 (by decide)) (append (widen s12988_4 (by decide)) (append (widen s12992_64 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide)))))))))))

theorem claim224 : CheckedClaim verifiedRow ⟨1,1,1,12986,14974,-46570343471,-12034870943⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12986 1989 ⟨-46570325160,-12034889254⟩
  rw [← get_eq_raw]
  exact (append (widen s12986_2 (by decide)) (append (widen s12988_4 (by decide)) (append (widen s12992_64 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_1024 (by decide)) (append (widen s14336_512 (by decide)) (append (widen s14848_64 (by decide)) (append (widen s14912_32 (by decide)) (append (widen s14944_16 (by decide)) (append (widen s14960_8 (by decide)) (append (widen s14968_4 (by decide)) (append (widen s14972_2 (by decide)) (widen s14974_1 (by decide))))))))))))))

theorem claim225 : CheckedClaim verifiedRow ⟨1,1,1,12986,15968,-46570343471,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 12986 2983 ⟨-46570325160,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s12986_2 (by decide)) (append (widen s12988_4 (by decide)) (append (widen s12992_64 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_1024 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))

theorem claim226 : CheckedClaim verifiedRow ⟨1,1,1,13018,16000,-45813579066,18313⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13018 2983 ⟨-45813560755,2⟩
  rw [← get_eq_raw]
  exact (append (widen s13018_2 (by decide)) (append (widen s13020_4 (by decide)) (append (widen s13024_32 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_1024 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))))

theorem claim227 : CheckedClaim verifiedRow ⟨1,1,1,13948,17924,-27087962561,24943092975⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13948 3977 ⟨-27087944250,24943074664⟩
  rw [← get_eq_raw]
  exact (append (widen s13948_4 (by decide)) (append (widen s13952_128 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_4 (by decide)) (widen s17924_1 (by decide)))))))))

theorem claim228 : CheckedClaim verifiedRow ⟨1,1,1,13948,19912,-27087962561,71444374508⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13948 5965 ⟨-27087944250,71444356197⟩
  rw [← get_eq_raw]
  exact (append (widen s13948_4 (by decide)) (append (widen s13952_128 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide))))))))))))

theorem claim229 : CheckedClaim verifiedRow ⟨1,1,1,13980,15471,-26543225142,-6014314226⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13980 1492 ⟨-26543206831,-6014332537⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_64 (by decide)) (append (widen s15424_32 (by decide)) (widen s15456_16 (by decide)))))))))

theorem claim230 : CheckedClaim verifiedRow ⟨1,1,1,13980,15968,-26543225142,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13980 1989 ⟨-26543206831,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim231 : CheckedClaim verifiedRow ⟨1,1,1,13980,16962,-26543225142,11227084404⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13980 2983 ⟨-26543206831,11227066093⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_512 (by decide)) (append (widen s16896_64 (by decide)) (append (widen s16960_2 (by decide)) (widen s16962_1 (by decide))))))))))

theorem claim232 : CheckedClaim verifiedRow ⟨1,1,1,13980,17956,-26543225142,25470878411⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13980 3977 ⟨-26543206831,25470860100⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide)))))))))))

theorem claim233 : CheckedClaim verifiedRow ⟨1,1,1,13980,19944,-26543225142,72469491435⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 13980 5965 ⟨-26543206831,72469473124⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))

theorem claim234 : CheckedClaim verifiedRow ⟨1,1,1,14012,16000,-26004226410,18313⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14012 1989 ⟨-26004208099,2⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim235 : CheckedClaim verifiedRow ⟨1,1,1,14012,17988,-26004226410,26004226410⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14012 3977 ⟨-26004208099,26004208099⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide))))))))))

private theorem s19456_512 : Run get 19456 512 ⟨57903379597,73212508044⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

theorem claim236 : CheckedClaim verifiedRow ⟨1,1,1,14012,19976,-26004226410,73504702286⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14012 5965 ⟨-26004208099,73504683975⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))))

theorem claim237 : CheckedClaim verifiedRow ⟨1,1,1,14044,16032,-25470878411,359669496⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14044 1989 ⟨-25470860100,359651185⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))

theorem claim238 : CheckedClaim verifiedRow ⟨1,1,1,14044,17026,-25470878411,12034907568⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14044 2983 ⟨-25470860100,12034889257⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_512 (by decide)) (append (widen s16896_128 (by decide)) (append (widen s17024_2 (by decide)) (widen s17026_1 (by decide)))))))))

theorem claim239 : CheckedClaim verifiedRow ⟨1,1,1,14044,20008,-25470878411,74550052275⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14044 5965 ⟨-25470860100,74550033964⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim240 : CheckedClaim verifiedRow ⟨1,1,1,14076,16064,-24943092975,719412458⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14076 1989 ⟨-24943074664,719394147⟩
  rw [← get_eq_raw]
  exact (append (widen s14076_4 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))

theorem claim241 : CheckedClaim verifiedRow ⟨1,1,1,14477,15471,-18764376507,-6014314226⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14477 995 ⟨-18764358196,-6014332537⟩
  rw [← get_eq_raw]
  exact (append (widen s14477_1 (by decide)) (append (widen s14478_2 (by decide)) (append (widen s14480_16 (by decide)) (append (widen s14496_32 (by decide)) (append (widen s14528_64 (by decide)) (append (widen s14592_256 (by decide)) (append (widen s14848_512 (by decide)) (append (widen s15360_64 (by decide)) (append (widen s15424_32 (by decide)) (widen s15456_16 (by decide)))))))))))

theorem claim242 : CheckedClaim verifiedRow ⟨1,1,1,14477,15968,-18764376507,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14477 1492 ⟨-18764358196,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s14477_1 (by decide)) (append (widen s14478_2 (by decide)) (append (widen s14480_16 (by decide)) (append (widen s14496_32 (by decide)) (append (widen s14528_64 (by decide)) (append (widen s14592_256 (by decide)) (append (widen s14848_512 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))))

theorem claim243 : CheckedClaim verifiedRow ⟨1,1,1,14974,15720,-12034907568,-3157043041⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14974 747 ⟨-12034889257,-3157061352⟩
  rw [← get_eq_raw]
  exact (append (widen s14974_2 (by decide)) (append (widen s14976_128 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_256 (by decide)) (append (widen s15616_64 (by decide)) (append (widen s15680_32 (by decide)) (append (widen s15712_8 (by decide)) (widen s15720_1 (by decide)))))))))

theorem claim244 : CheckedClaim verifiedRow ⟨1,1,1,14974,17956,-12034907568,25470878411⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 14974 2983 ⟨-12034889257,25470860100⟩
  rw [← get_eq_raw]
  exact (append (widen s14974_2 (by decide)) (append (widen s14976_128 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_1024 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide))))))))))

theorem claim245 : CheckedClaim verifiedRow ⟨1,1,1,15038,18020,-11227084404,26543225142⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15038 2983 ⟨-11227066093,26543206831⟩
  rw [← get_eq_raw]
  exact (append (widen s15038_2 (by decide)) (append (widen s15040_64 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_1024 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide)))))))))))

theorem claim246 : CheckedClaim verifiedRow ⟨1,1,1,15223,15719,-8951382928,-3168391847⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15223 497 ⟨-8951364617,-3168410158⟩
  rw [← get_eq_raw]
  exact (append (widen s15223_1 (by decide)) (append (widen s15224_8 (by decide)) (append (widen s15232_128 (by decide)) (append (widen s15360_256 (by decide)) (append (widen s15616_64 (by decide)) (append (widen s15680_32 (by decide)) (widen s15712_8 (by decide))))))))

theorem claim247 : CheckedClaim verifiedRow ⟨1,1,1,15223,15968,-8951382928,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15223 746 ⟨-8951364617,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s15223_1 (by decide)) (append (widen s15224_8 (by decide)) (append (widen s15232_128 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))

theorem claim248 : CheckedClaim verifiedRow ⟨1,1,1,15471,15843,-6014350851,-1766251764⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15471 373 ⟨-6014332540,-1766270075⟩
  rw [← get_eq_raw]
  exact (append (widen s15471_1 (by decide)) (append (widen s15472_16 (by decide)) (append (widen s15488_128 (by decide)) (append (widen s15616_128 (by decide)) (append (widen s15744_64 (by decide)) (append (widen s15808_32 (by decide)) (widen s15840_4 (by decide))))))))

theorem claim249 : CheckedClaim verifiedRow ⟨1,1,1,15471,15968,-6014350851,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15471 498 ⟨-6014332540,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s15471_1 (by decide)) (append (widen s15472_16 (by decide)) (append (widen s15488_128 (by decide)) (append (widen s15616_256 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))

theorem claim250 : CheckedClaim verifiedRow ⟨1,1,1,15595,15844,-4582669609,-1754978843⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15595 250 ⟨-4582651298,-1754997154⟩
  rw [← get_eq_raw]
  exact (append (widen s15595_1 (by decide)) (append (widen s15596_4 (by decide)) (append (widen s15600_16 (by decide)) (append (widen s15616_128 (by decide)) (append (widen s15744_64 (by decide)) (append (widen s15808_32 (by decide)) (append (widen s15840_4 (by decide)) (widen s15844_1 (by decide)))))))))

theorem claim251 : CheckedClaim verifiedRow ⟨1,1,1,15719,15905,-3168428472,-1068050959⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15719 187 ⟨-3168410161,-1068069270⟩
  rw [← get_eq_raw]
  exact (append (widen s15719_1 (by decide)) (append (widen s15720_8 (by decide)) (append (widen s15728_16 (by decide)) (append (widen s15744_128 (by decide)) (append (widen s15872_32 (by decide)) (widen s15904_2 (by decide)))))))

theorem claim252 : CheckedClaim verifiedRow ⟨1,1,1,15719,15968,-3168428472,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15719 250 ⟨-3168410161,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s15719_1 (by decide)) (append (widen s15720_8 (by decide)) (append (widen s15728_16 (by decide)) (append (widen s15744_128 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))

theorem claim253 : CheckedClaim verifiedRow ⟨1,1,1,15781,15906,-2466179522,-1056799831⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15781 126 ⟨-2466161211,-1056818142⟩
  rw [← get_eq_raw]
  exact (append (widen s15781_1 (by decide)) (append (widen s15782_2 (by decide)) (append (widen s15784_8 (by decide)) (append (widen s15792_16 (by decide)) (append (widen s15808_64 (by decide)) (append (widen s15872_32 (by decide)) (append (widen s15904_2 (by decide)) (widen s15906_1 (by decide)))))))))

theorem claim254 : CheckedClaim verifiedRow ⟨1,1,1,15843,15968,-1766288389,-359632871⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15843 126 ⟨-1766270078,-359651182⟩
  rw [← get_eq_raw]
  exact (append (widen s15843_1 (by decide)) (append (widen s15844_4 (by decide)) (append (widen s15848_8 (by decide)) (append (widen s15856_16 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))

theorem claim255 : CheckedClaim verifiedRow ⟨1,1,1,15843,16031,-1766288389,348429484⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15843 189 ⟨-1766270078,348411173⟩
  rw [← get_eq_raw]
  exact (append (widen s15843_1 (by decide)) (append (widen s15844_4 (by decide)) (append (widen s15848_8 (by decide)) (append (widen s15856_16 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_32 (by decide)))))))

theorem claim256 : CheckedClaim verifiedRow ⟨1,1,1,15843,16093,-1766288389,1045585591⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15843 251 ⟨-1766270078,1045567280⟩
  rw [← get_eq_raw]
  exact (append (widen s15843_1 (by decide)) (append (widen s15844_4 (by decide)) (append (widen s15848_8 (by decide)) (append (widen s15856_16 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (append (widen s16064_16 (by decide)) (append (widen s16080_8 (by decide)) (append (widen s16088_4 (by decide)) (widen s16092_2 (by decide)))))))))))

theorem claim257 : CheckedClaim verifiedRow ⟨1,1,1,15844,16216,-1755015468,2432264909⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15844 373 ⟨-1754997157,2432246598⟩
  rw [← get_eq_raw]
  exact (append (widen s15844_4 (by decide)) (append (widen s15848_8 (by decide)) (append (widen s15856_16 (by decide)) (append (widen s15872_256 (by decide)) (append (widen s16128_64 (by decide)) (append (widen s16192_16 (by decide)) (append (widen s16208_8 (by decide)) (widen s16216_1 (by decide)))))))))

theorem claim258 : CheckedClaim verifiedRow ⟨1,1,1,15905,16000,-1068087584,18313⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15905 96 ⟨-1068069273,2⟩
  rw [← get_eq_raw]
  exact (append (widen s15905_1 (by decide)) (append (widen s15906_2 (by decide)) (append (widen s15908_4 (by decide)) (append (widen s15912_8 (by decide)) (append (widen s15920_16 (by decide)) (append (widen s15936_64 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim259 : CheckedClaim verifiedRow ⟨1,1,1,15936,15984,-719412458,-179801543⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15936 49 ⟨-719394147,-179819854⟩
  rw [← get_eq_raw]
  exact (append (widen s15936_32 (by decide)) (append (widen s15968_16 (by decide)) (widen s15984_1 (by decide))))

theorem claim260 : CheckedClaim verifiedRow ⟨1,1,1,15936,19912,-719412458,71444374508⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15936 3977 ⟨-719394147,71444356197⟩
  rw [← get_eq_raw]
  exact (append (widen s15936_64 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide)))))))))))

private theorem s19968_512 : Run get 19968 512 ⟨73244932458,91134231691⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨57903379597,91134231691⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨34026163659,91134231691⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨4342062397,91134231691⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨91171868246,111773587958⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨111816590217,135145756440⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨91171868246,135145756440⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

theorem claim261 : CheckedClaim verifiedRow ⟨1,1,1,15936,21900,-719412458,155071788427⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15936 5965 ⟨-719394147,155071770116⟩
  rw [← get_eq_raw]
  exact (append (widen s15936_64 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_8 (by decide)) (append (widen s21896_4 (by decide)) (widen s21900_1 (by decide)))))))))))

theorem claim262 : CheckedClaim verifiedRow ⟨1,1,1,15953,15983,-528281987,-191040546⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15953 31 ⟨-528263676,-191058857⟩
  rw [← get_eq_raw]
  exact (append (widen s15953_1 (by decide)) (append (widen s15954_2 (by decide)) (append (widen s15956_4 (by decide)) (append (widen s15960_8 (by decide)) (widen s15968_16 (by decide))))))

theorem claim263 : CheckedClaim verifiedRow ⟨1,1,1,15953,15999,-528281987,-11220309⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15953 47 ⟨-528263676,-11238620⟩
  rw [← get_eq_raw]
  exact (append (widen s15953_1 (by decide)) (append (widen s15954_2 (by decide)) (append (widen s15956_4 (by decide)) (append (widen s15960_8 (by decide)) (widen s15968_32 (by decide))))))

theorem claim264 : CheckedClaim verifiedRow ⟨1,1,1,15968,15991,-359669496,-101129621⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 24 ⟨-359651185,-101147932⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_16 (by decide)) (widen s15984_8 (by decide)))

theorem claim265 : CheckedClaim verifiedRow ⟨1,1,1,15968,16015,-359669496,168599210⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 48 ⟨-359651185,168580899⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (widen s16000_16 (by decide)))

theorem claim266 : CheckedClaim verifiedRow ⟨1,1,1,15968,16155,-359669496,1743742983⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 188 ⟨-359651185,1743724672⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_16 (by decide)) (append (widen s16144_8 (by decide)) (widen s16152_4 (by decide))))))

theorem claim267 : CheckedClaim verifiedRow ⟨1,1,1,15968,16341,-359669496,3850897861⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 374 ⟨-359651185,3850879550⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_128 (by decide)) (append (widen s16256_64 (by decide)) (append (widen s16320_16 (by decide)) (append (widen s16336_4 (by decide)) (widen s16340_2 (by decide))))))))

theorem claim268 : CheckedClaim verifiedRow ⟨1,1,1,15968,16714,-359669496,8194295425⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 747 ⟨-359651185,8194277114⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_256 (by decide)) (append (widen s16640_64 (by decide)) (append (widen s16704_8 (by decide)) (append (widen s16712_2 (by decide)) (widen s16714_1 (by decide)))))))))

theorem claim269 : CheckedClaim verifiedRow ⟨1,1,1,15968,17459,-359669496,17846082876⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 1492 ⟨-359651185,17846064565⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_32 (by decide)) (append (widen s17440_16 (by decide)) (widen s17456_4 (by decide))))))))

theorem claim270 : CheckedClaim verifiedRow ⟨1,1,1,15968,17956,-359669496,25470878411⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 1989 ⟨-359651185,25470860100⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide)))))))))

theorem claim271 : CheckedClaim verifiedRow ⟨1,1,1,15968,18950,-359669496,45065036677⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 2983 ⟨-359651185,45065018366⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_512 (by decide)) (append (widen s18944_4 (by decide)) (append (widen s18948_2 (by decide)) (widen s18950_1 (by decide)))))))))

theorem claim272 : CheckedClaim verifiedRow ⟨1,1,1,15968,19944,-359669496,72469491435⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 3977 ⟨-359651185,72469473124⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))

theorem claim273 : CheckedClaim verifiedRow ⟨1,1,1,15968,21932,-359669496,156742670599⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15968 5965 ⟨-359651185,156742652288⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_32 (by decide)) (append (widen s21920_8 (by decide)) (append (widen s21928_4 (by decide)) (widen s21932_1 (by decide))))))))))))

theorem claim274 : CheckedClaim verifiedRow ⟨1,1,1,15976,15991,-269751681,-101129621⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15976 16 ⟨-269733370,-101147932⟩
  rw [← get_eq_raw]
  exact (append (widen s15976_8 (by decide)) (widen s15984_8 (by decide)))

theorem claim275 : CheckedClaim verifiedRow ⟨1,1,1,15976,15999,-269751681,-11220309⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15976 24 ⟨-269733370,-11238620⟩
  rw [← get_eq_raw]
  exact (append (widen s15976_8 (by decide)) (widen s15984_16 (by decide)))

theorem claim276 : CheckedClaim verifiedRow ⟨1,1,1,15983,15991,-191077171,-101129621⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15983 9 ⟨-191058860,-101147932⟩
  rw [← get_eq_raw]
  exact (append (widen s15983_1 (by decide)) (widen s15984_8 (by decide)))

theorem claim277 : CheckedClaim verifiedRow ⟨1,1,1,15983,15995,-191077171,-56174853⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15983 13 ⟨-191058860,-56193164⟩
  rw [← get_eq_raw]
  exact (append (widen s15983_1 (by decide)) (append (widen s15984_8 (by decide)) (widen s15992_4 (by decide))))

theorem claim278 : CheckedClaim verifiedRow ⟨1,1,1,15984,16031,-179838168,348429484⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15984 48 ⟨-179819857,348411173⟩
  rw [← get_eq_raw]
  exact (append (widen s15984_16 (by decide)) (widen s16000_32 (by decide)))

theorem claim279 : CheckedClaim verifiedRow ⟨1,1,1,15987,15995,-146121417,-56174853⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15987 9 ⟨-146103106,-56193164⟩
  rw [← get_eq_raw]
  exact (append (widen s15987_1 (by decide)) (append (widen s15988_4 (by decide)) (widen s15992_4 (by decide))))

theorem claim280 : CheckedClaim verifiedRow ⟨1,1,1,15987,15999,-146121417,-11220309⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15987 13 ⟨-146103106,-11238620⟩
  rw [← get_eq_raw]
  exact (append (widen s15987_1 (by decide)) (append (widen s15988_4 (by decide)) (widen s15992_8 (by decide))))

theorem claim281 : CheckedClaim verifiedRow ⟨1,1,1,15991,15997,-101166246,-33697564⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15991 7 ⟨-101147935,-33715875⟩
  rw [← get_eq_raw]
  exact (append (widen s15991_1 (by decide)) (append (widen s15992_4 (by decide)) (widen s15996_2 (by decide))))

theorem claim282 : CheckedClaim verifiedRow ⟨1,1,1,15991,15999,-101166246,-11220309⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15991 9 ⟨-101147935,-11238620⟩
  rw [← get_eq_raw]
  exact (append (widen s15991_1 (by decide)) (widen s15992_8 (by decide)))

theorem claim283 : CheckedClaim verifiedRow ⟨1,1,1,15993,15999,-78688823,-11220309⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15993 7 ⟨-78670512,-11238620⟩
  rw [← get_eq_raw]
  exact (append (widen s15993_1 (by decide)) (append (widen s15994_2 (by decide)) (widen s15996_4 (by decide))))

theorem claim284 : CheckedClaim verifiedRow ⟨1,1,1,15995,15998,-56211478,-22458934⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15995 4 ⟨-56193167,-22477245⟩
  rw [← get_eq_raw]
  exact (append (widen s15995_1 (by decide)) (append (widen s15996_2 (by decide)) (widen s15998_1 (by decide))))

theorem claim285 : CheckedClaim verifiedRow ⟨1,1,1,15995,16001,-56211478,11256934⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15995 7 ⟨-56193167,11238623⟩
  rw [← get_eq_raw]
  exact (append (widen s15995_1 (by decide)) (append (widen s15996_4 (by decide)) (widen s16000_2 (by decide))))

theorem claim286 : CheckedClaim verifiedRow ⟨1,1,1,15995,16007,-56211478,78688823⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15995 13 ⟨-56193167,78670512⟩
  rw [← get_eq_raw]
  exact (append (widen s15995_1 (by decide)) (append (widen s15996_4 (by decide)) (widen s16000_8 (by decide))))

theorem claim287 : CheckedClaim verifiedRow ⟨1,1,1,15996,15999,-44972828,-11220309⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15996 4 ⟨-44954517,-11238620⟩
  rw [← get_eq_raw]
  exact (widen s15996_4 (by decide))

theorem claim288 : CheckedClaim verifiedRow ⟨1,1,1,15997,16003,-33734189,33734189⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15997 7 ⟨-33715878,33715878⟩
  rw [← get_eq_raw]
  exact (append (widen s15997_1 (by decide)) (append (widen s15998_2 (by decide)) (widen s16000_4 (by decide))))

theorem claim289 : CheckedClaim verifiedRow ⟨1,1,1,15999,16003,-11256934,33734189⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15999 5 ⟨-11238623,33715878⟩
  rw [← get_eq_raw]
  exact (append (widen s15999_1 (by decide)) (widen s16000_4 (by decide)))

theorem claim290 : CheckedClaim verifiedRow ⟨1,1,1,15999,16007,-11256934,78688823⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15999 9 ⟨-11238623,78670512⟩
  rw [← get_eq_raw]
  exact (append (widen s15999_1 (by decide)) (widen s16000_8 (by decide)))

theorem claim291 : CheckedClaim verifiedRow ⟨1,1,1,15999,16015,-11256934,168599210⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15999 17 ⟨-11238623,168580899⟩
  rw [← get_eq_raw]
  exact (append (widen s15999_1 (by decide)) (widen s16000_16 (by decide)))

theorem claim292 : CheckedClaim verifiedRow ⟨1,1,1,15999,16062,-11256934,696924097⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 15999 64 ⟨-11238623,696905786⟩
  rw [← get_eq_raw]
  exact (append (widen s15999_1 (by decide)) (append (widen s16000_32 (by decide)) (append (widen s16032_16 (by decide)) (append (widen s16048_8 (by decide)) (append (widen s16056_4 (by decide)) (append (widen s16060_2 (by decide)) (widen s16062_1 (by decide))))))))

theorem claim293 : CheckedClaim verifiedRow ⟨1,1,1,16000,16062,-18313,696924097⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16000 63 ⟨-2,696905786⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_32 (by decide)) (append (widen s16032_16 (by decide)) (append (widen s16048_8 (by decide)) (append (widen s16056_4 (by decide)) (append (widen s16060_2 (by decide)) (widen s16062_1 (by decide)))))))

theorem claim294 : CheckedClaim verifiedRow ⟨1,1,1,16000,16093,-18313,1045585591⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16000 94 ⟨-2,1045567280⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_64 (by decide)) (append (widen s16064_16 (by decide)) (append (widen s16080_8 (by decide)) (append (widen s16088_4 (by decide)) (widen s16092_2 (by decide))))))

theorem claim295 : CheckedClaim verifiedRow ⟨1,1,1,16000,17988,-18313,26004226410⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16000 1989 ⟨-2,26004208099⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide))))))))

theorem claim296 : CheckedClaim verifiedRow ⟨1,1,1,16000,19976,-18313,73504702286⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16000 3977 ⟨-2,73504683975⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))

theorem claim297 : CheckedClaim verifiedRow ⟨1,1,1,16000,21964,-18313,158422830697⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16000 5965 ⟨-2,158422812386⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide)))))))))))

theorem claim298 : CheckedClaim verifiedRow ⟨1,1,1,16001,16005,11220309,56211478⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16001 5 ⟨11238620,56193167⟩
  rw [← get_eq_raw]
  exact (append (widen s16001_1 (by decide)) (append (widen s16002_2 (by decide)) (widen s16004_2 (by decide))))

theorem claim299 : CheckedClaim verifiedRow ⟨1,1,1,16001,16007,11220309,78688823⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16001 7 ⟨11238620,78670512⟩
  rw [← get_eq_raw]
  exact (append (widen s16001_1 (by decide)) (append (widen s16002_2 (by decide)) (widen s16004_4 (by decide))))

theorem claim300 : CheckedClaim verifiedRow ⟨1,1,1,16003,16009,33697564,101166246⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16003 7 ⟨33715875,101147935⟩
  rw [← get_eq_raw]
  exact (append (widen s16003_1 (by decide)) (append (widen s16004_4 (by decide)) (widen s16008_2 (by decide))))

theorem claim301 : CheckedClaim verifiedRow ⟨1,1,1,16003,16011,33697564,123643770⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16003 9 ⟨33715875,123625459⟩
  rw [← get_eq_raw]
  exact (append (widen s16003_1 (by decide)) (append (widen s16004_4 (by decide)) (widen s16008_4 (by decide))))

theorem claim302 : CheckedClaim verifiedRow ⟨1,1,1,16003,16015,33697564,168599210⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16003 13 ⟨33715875,168580899⟩
  rw [← get_eq_raw]
  exact (append (widen s16003_1 (by decide)) (append (widen s16004_4 (by decide)) (widen s16008_8 (by decide))))

theorem claim303 : CheckedClaim verifiedRow ⟨1,1,1,16007,16023,78652198,258512286⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16007 17 ⟨78670509,258493975⟩
  rw [← get_eq_raw]
  exact (append (widen s16007_1 (by decide)) (append (widen s16008_8 (by decide)) (widen s16016_8 (by decide))))

theorem claim304 : CheckedClaim verifiedRow ⟨1,1,1,16007,16031,78652198,348429484⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16007 25 ⟨78670509,348411173⟩
  rw [← get_eq_raw]
  exact (append (widen s16007_1 (by decide)) (append (widen s16008_8 (by decide)) (widen s16016_16 (by decide))))

theorem claim305 : CheckedClaim verifiedRow ⟨1,1,1,16015,16047,168562585,528281987⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16015 33 ⟨168580896,528263676⟩
  rw [← get_eq_raw]
  exact (append (widen s16015_1 (by decide)) (append (widen s16016_16 (by decide)) (widen s16032_16 (by decide))))

theorem claim306 : CheckedClaim verifiedRow ⟨1,1,1,16015,16062,168562585,696924097⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16015 48 ⟨168580896,696905786⟩
  rw [← get_eq_raw]
  exact (append (widen s16015_1 (by decide)) (append (widen s16016_16 (by decide)) (append (widen s16032_16 (by decide)) (append (widen s16048_8 (by decide)) (append (widen s16056_4 (by decide)) (append (widen s16060_2 (by decide)) (widen s16062_1 (by decide))))))))

theorem claim307 : CheckedClaim verifiedRow ⟨1,1,1,16030,16155,337152935,1743742983⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16030 126 ⟨337171246,1743724672⟩
  rw [← get_eq_raw]
  exact (append (widen s16030_2 (by decide)) (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_16 (by decide)) (append (widen s16144_8 (by decide)) (widen s16152_4 (by decide)))))))

theorem claim308 : CheckedClaim verifiedRow ⟨1,1,1,16031,16093,348392859,1045585591⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16031 63 ⟨348411170,1045567280⟩
  rw [← get_eq_raw]
  exact (append (widen s16031_1 (by decide)) (append (widen s16032_32 (by decide)) (append (widen s16064_16 (by decide)) (append (widen s16080_8 (by decide)) (append (widen s16088_4 (by decide)) (widen s16092_2 (by decide)))))))

theorem claim309 : CheckedClaim verifiedRow ⟨1,1,1,16031,16155,348392859,1743742983⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16031 125 ⟨348411170,1743724672⟩
  rw [← get_eq_raw]
  exact (append (widen s16031_1 (by decide)) (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_16 (by decide)) (append (widen s16144_8 (by decide)) (widen s16152_4 (by decide)))))))

theorem claim310 : CheckedClaim verifiedRow ⟨1,1,1,16031,16217,348392859,2443569171⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16031 187 ⟨348411170,2443550860⟩
  rw [← get_eq_raw]
  exact (append (widen s16031_1 (by decide)) (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_64 (by decide)) (append (widen s16192_16 (by decide)) (append (widen s16208_8 (by decide)) (widen s16216_2 (by decide))))))))

theorem claim311 : CheckedClaim verifiedRow ⟨1,1,1,16032,18020,359632871,26543225142⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16032 1989 ⟨359651182,26543206831⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))

theorem claim312 : CheckedClaim verifiedRow ⟨1,1,1,16032,20008,359632871,74550052275⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16032 3977 ⟨359651182,74550033964⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))

theorem claim313 : CheckedClaim verifiedRow ⟨1,1,1,16032,21996,359632871,160112177865⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16032 5965 ⟨359651182,160112159554⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide)))))))))))))

theorem claim314 : CheckedClaim verifiedRow ⟨1,1,1,16064,20040,719375833,75605585260⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16064 3977 ⟨719394144,75605566949⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide)))))))))

theorem claim315 : CheckedClaim verifiedRow ⟨1,1,1,16092,16341,1034298362,3850897861⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16092 250 ⟨1034316673,3850879550⟩
  rw [← get_eq_raw]
  exact (append (widen s16092_4 (by decide)) (append (widen s16096_32 (by decide)) (append (widen s16128_128 (by decide)) (append (widen s16256_64 (by decide)) (append (widen s16320_16 (by decide)) (append (widen s16336_4 (by decide)) (widen s16340_2 (by decide))))))))

theorem claim316 : CheckedClaim verifiedRow ⟨1,1,1,16093,16217,1045548966,2443569171⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16093 125 ⟨1045567277,2443550860⟩
  rw [← get_eq_raw]
  exact (append (widen s16093_1 (by decide)) (append (widen s16094_2 (by decide)) (append (widen s16096_32 (by decide)) (append (widen s16128_64 (by decide)) (append (widen s16192_16 (by decide)) (append (widen s16208_8 (by decide)) (widen s16216_2 (by decide))))))))

theorem claim317 : CheckedClaim verifiedRow ⟨1,1,1,16093,16465,1045548966,5272911133⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16093 373 ⟨1045567277,5272892822⟩
  rw [← get_eq_raw]
  exact (append (widen s16093_1 (by decide)) (append (widen s16094_2 (by decide)) (append (widen s16096_32 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_64 (by decide)) (append (widen s16448_16 (by decide)) (widen s16464_2 (by decide))))))))

theorem claim318 : CheckedClaim verifiedRow ⟨1,1,1,16216,16714,2432228284,8194295425⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16216 499 ⟨2432246595,8194277114⟩
  rw [← get_eq_raw]
  exact (append (widen s16216_8 (by decide)) (append (widen s16224_32 (by decide)) (append (widen s16256_128 (by decide)) (append (widen s16384_256 (by decide)) (append (widen s16640_64 (by decide)) (append (widen s16704_8 (by decide)) (append (widen s16712_2 (by decide)) (widen s16714_1 (by decide)))))))))

theorem claim319 : CheckedClaim verifiedRow ⟨1,1,1,16217,16962,2443532546,11227084404⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16217 746 ⟨2443550857,11227066093⟩
  rw [← get_eq_raw]
  exact (append (widen s16217_1 (by decide)) (append (widen s16218_2 (by decide)) (append (widen s16220_4 (by decide)) (append (widen s16224_32 (by decide)) (append (widen s16256_128 (by decide)) (append (widen s16384_512 (by decide)) (append (widen s16896_64 (by decide)) (append (widen s16960_2 (by decide)) (widen s16962_1 (by decide))))))))))

theorem claim320 : CheckedClaim verifiedRow ⟨1,1,1,16465,17459,5272874508,17846082876⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16465 995 ⟨5272892819,17846064565⟩
  rw [← get_eq_raw]
  exact (append (widen s16465_1 (by decide)) (append (widen s16466_2 (by decide)) (append (widen s16468_4 (by decide)) (append (widen s16472_8 (by decide)) (append (widen s16480_32 (by decide)) (append (widen s16512_128 (by decide)) (append (widen s16640_256 (by decide)) (append (widen s16896_512 (by decide)) (append (widen s17408_32 (by decide)) (append (widen s17440_16 (by decide)) (widen s17456_4 (by decide))))))))))))

theorem claim321 : CheckedClaim verifiedRow ⟨1,1,1,16465,17956,5272874508,25470878411⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16465 1492 ⟨5272892819,25470860100⟩
  rw [← get_eq_raw]
  exact (append (widen s16465_1 (by decide)) (append (widen s16466_2 (by decide)) (append (widen s16468_4 (by decide)) (append (widen s16472_8 (by decide)) (append (widen s16480_32 (by decide)) (append (widen s16512_128 (by decide)) (append (widen s16640_256 (by decide)) (append (widen s16896_512 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide)))))))))))))

theorem claim322 : CheckedClaim verifiedRow ⟨1,1,1,16962,18950,11227047779,45065036677⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16962 1989 ⟨11227066090,45065018366⟩
  rw [← get_eq_raw]
  exact (append (widen s16962_2 (by decide)) (append (widen s16964_4 (by decide)) (append (widen s16968_8 (by decide)) (append (widen s16976_16 (by decide)) (append (widen s16992_32 (by decide)) (append (widen s17024_128 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_1024 (by decide)) (append (widen s18432_512 (by decide)) (append (widen s18944_4 (by decide)) (append (widen s18948_2 (by decide)) (widen s18950_1 (by decide)))))))))))))

theorem claim323 : CheckedClaim verifiedRow ⟨1,1,1,16962,19944,11227047779,72469491435⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 16962 2983 ⟨11227066090,72469473124⟩
  rw [← get_eq_raw]
  exact (append (widen s16962_2 (by decide)) (append (widen s16964_4 (by decide)) (append (widen s16968_8 (by decide)) (append (widen s16976_16 (by decide)) (append (widen s16992_32 (by decide)) (append (widen s17024_128 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_1024 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))))

theorem claim324 : CheckedClaim verifiedRow ⟨1,1,1,17956,19944,25470841786,72469491435⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 17956 1989 ⟨25470860097,72469473124⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))

theorem claim325 : CheckedClaim verifiedRow ⟨1,1,1,17956,20938,25470841786,109509479734⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 17956 2983 ⟨25470860097,109509461423⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_256 (by decide)) (append (widen s20736_128 (by decide)) (append (widen s20864_64 (by decide)) (append (widen s20928_8 (by decide)) (append (widen s20936_2 (by decide)) (widen s20938_1 (by decide))))))))))))))

theorem claim326 : CheckedClaim verifiedRow ⟨1,1,1,17956,21932,25470841786,156742670599⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 17956 3977 ⟨25470860097,156742652288⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_32 (by decide)) (append (widen s21920_8 (by decide)) (append (widen s21928_4 (by decide)) (widen s21932_1 (by decide)))))))))))))))

theorem claim327 : CheckedClaim verifiedRow ⟨1,1,1,17988,19976,26004189785,73504702286⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 17988 1989 ⟨26004208096,73504683975⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide)))))))))))

theorem claim328 : CheckedClaim verifiedRow ⟨1,1,1,17988,21964,26004189785,158422830697⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 17988 3977 ⟨26004208096,158422812386⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide)))))))))))))))

private theorem s21504_512 : Run get 21504 512 ⟨135194020114,161119517986⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨161172625271,189390208868⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨135194020114,189390208868⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨91171868246,189390208868⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨189447379505,219457752999⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨219517808552,250613188274⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨189447379505,250613188274⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

theorem claim329 : CheckedClaim verifiedRow ⟨1,1,1,17988,23952,26004189785,275185384947⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 17988 5965 ⟨26004208096,275185366636⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide))))))))))))))

theorem claim330 : CheckedClaim verifiedRow ⟨1,1,1,18020,20008,26543188517,74550052275⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 18020 1989 ⟨26543206828,74550033964⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim331 : CheckedClaim verifiedRow ⟨1,1,1,18020,23984,26543188517,277135607154⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 18020 5965 ⟨26543206828,277135588843⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))))

theorem claim332 : CheckedClaim verifiedRow ⟨1,1,1,18052,20040,27087925936,75605585260⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 18052 1989 ⟨27087944247,75605566949⟩
  rw [← get_eq_raw]
  exact (append (widen s18052_4 (by decide)) (append (widen s18056_8 (by decide)) (append (widen s18064_16 (by decide)) (append (widen s18080_32 (by decide)) (append (widen s18112_64 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide))))))))))))

theorem claim333 : CheckedClaim verifiedRow ⟨1,1,1,18950,20938,45065000052,109509479734⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 18950 1989 ⟨45065018363,109509461423⟩
  rw [← get_eq_raw]
  exact (append (widen s18950_2 (by decide)) (append (widen s18952_8 (by decide)) (append (widen s18960_16 (by decide)) (append (widen s18976_32 (by decide)) (append (widen s19008_64 (by decide)) (append (widen s19072_128 (by decide)) (append (widen s19200_256 (by decide)) (append (widen s19456_1024 (by decide)) (append (widen s20480_256 (by decide)) (append (widen s20736_128 (by decide)) (append (widen s20864_64 (by decide)) (append (widen s20928_8 (by decide)) (append (widen s20936_2 (by decide)) (widen s20938_1 (by decide)))))))))))))))

theorem claim334 : CheckedClaim verifiedRow ⟨1,1,1,18950,21932,45065000052,156742670599⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 18950 2983 ⟨45065018363,156742652288⟩
  rw [← get_eq_raw]
  exact (append (widen s18950_2 (by decide)) (append (widen s18952_8 (by decide)) (append (widen s18960_16 (by decide)) (append (widen s18976_32 (by decide)) (append (widen s19008_64 (by decide)) (append (widen s19072_128 (by decide)) (append (widen s19200_256 (by decide)) (append (widen s19456_1024 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_32 (by decide)) (append (widen s21920_8 (by decide)) (append (widen s21928_4 (by decide)) (widen s21932_1 (by decide))))))))))))))))

theorem claim335 : CheckedClaim verifiedRow ⟨1,1,1,19944,22926,72469454810,212700098458⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 19944 2983 ⟨72469473121,212700080147⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_256 (by decide)) (append (widen s22784_128 (by decide)) (append (widen s22912_8 (by decide)) (append (widen s22920_4 (by decide)) (append (widen s22924_2 (by decide)) (widen s22926_1 (by decide)))))))))))

theorem claim336 : CheckedClaim verifiedRow ⟨1,1,1,19944,23920,72469454810,273232522183⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 19944 3977 ⟨72469473121,273232503872⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))

theorem claim337 : CheckedClaim verifiedRow ⟨1,1,1,19976,21964,73504665661,158422830697⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 19976 1989 ⟨73504683972,158422812386⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide))))))))))))))

theorem claim338 : CheckedClaim verifiedRow ⟨1,1,1,20008,21996,74550015650,160112177865⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 20008 1989 ⟨74550033961,160112159554⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide))))))))))))))

theorem claim339 : CheckedClaim verifiedRow ⟨1,1,1,20008,23984,74550015650,277135607154⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 20008 3977 ⟨74550033961,277135588843⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide)))))))))))))

theorem claim340 : CheckedClaim verifiedRow ⟨1,1,1,20040,22028,75605548635,161810618270⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 20040 1989 ⟨75605566946,161810599959⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_512 (by decide)) (append (widen s22016_8 (by decide)) (append (widen s22024_4 (by decide)) (widen s22028_1 (by decide)))))))))))

theorem claim341 : CheckedClaim verifiedRow ⟨1,1,1,20040,24016,75605548635,279082901235⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 20040 3977 ⟨75605566946,279082882924⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim342 : CheckedClaim verifiedRow ⟨1,1,1,20938,23920,109509443109,273232522183⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 20938 2983 ⟨109509461420,273232503872⟩
  rw [← get_eq_raw]
  exact (append (widen s20938_2 (by decide)) (append (widen s20940_4 (by decide)) (append (widen s20944_16 (by decide)) (append (widen s20960_32 (by decide)) (append (widen s20992_512 (by decide)) (append (widen s21504_1024 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))))

private theorem s23552_512 : Run get 23552 512 ⟨250674536370,281937053351⟩ :=
  join s23552_256 s23808_256 (by decide) (by decide)

private theorem s24064_512 : Run get 24064 512 ⟨281997698156,312312568279⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s23552_1024 : Run get 23552 1024 ⟨250674536370,312312568279⟩ :=
  join s23552_512 s24064_512 (by decide) (by decide)

private theorem s22528_2048 : Run get 22528 2048 ⟨189447379505,312312568279⟩ :=
  join s22528_1024 s23552_1024 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨312370152260,340455693668⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨340507573600,364962902933⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨312370152260,364962902933⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

theorem claim343 : CheckedClaim verifiedRow ⟨1,1,1,21900,25876,155071751802,376191190580⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 21900 3977 ⟨155071770113,376191172269⟩
  rw [← get_eq_raw]
  exact (append (widen s21900_4 (by decide)) (append (widen s21904_16 (by decide)) (append (widen s21920_32 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_16 (by decide)) (append (widen s25872_4 (by decide)) (widen s25876_1 (by decide))))))))))))

private theorem s25600_512 : Run get 25600 512 ⟨365006260334,384375921374⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨384407904196,397260902052⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨365006260334,397260902052⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨312370152260,397260902052⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨397278790895,402297699529⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨398373279460,402326443510⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨397278790895,402326443510⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

theorem claim344 : CheckedClaim verifiedRow ⟨1,1,1,21900,27864,155071751802,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 21900 5965 ⟨155071770113,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s21900_4 (by decide)) (append (widen s21904_16 (by decide)) (append (widen s21920_32 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_16 (by decide)) (append (widen s27856_8 (by decide)) (widen s27864_1 (by decide))))))))))))))

theorem claim345 : CheckedClaim verifiedRow ⟨1,1,1,21932,25908,156742633974,377381704443⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 21932 3977 ⟨156742652285,377381686132⟩
  rw [← get_eq_raw]
  exact (append (widen s21932_4 (by decide)) (append (widen s21936_16 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_32 (by decide)) (append (widen s25888_16 (by decide)) (append (widen s25904_4 (by decide)) (widen s25908_1 (by decide))))))))))))

theorem claim346 : CheckedClaim verifiedRow ⟨1,1,1,21932,27896,156742633974,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 21932 5965 ⟨156742652285,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s21932_4 (by decide)) (append (widen s21936_16 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide))))))))))))))

theorem claim347 : CheckedClaim verifiedRow ⟨1,1,1,21964,25940,158422794072,378548880960⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 21964 3977 ⟨158422812383,378548862649⟩
  rw [← get_eq_raw]
  exact (append (widen s21964_4 (by decide)) (append (widen s21968_16 (by decide)) (append (widen s21984_32 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_16 (by decide)) (append (widen s25936_4 (by decide)) (widen s25940_1 (by decide))))))))))))

theorem claim348 : CheckedClaim verifiedRow ⟨1,1,1,21964,27928,158422794072,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 21964 5965 ⟨158422812383,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s21964_4 (by decide)) (append (widen s21968_16 (by decide)) (append (widen s21984_32 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide))))))))))))

theorem claim349 : CheckedClaim verifiedRow ⟨1,1,1,21996,23984,160112141240,277135607154⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 21996 1989 ⟨160112159551,277135588843⟩
  rw [← get_eq_raw]
  exact (append (widen s21996_4 (by decide)) (append (widen s22000_16 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))

theorem claim350 : CheckedClaim verifiedRow ⟨1,1,1,22028,24016,161810581645,279082901235⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 22028 1989 ⟨161810599956,279082882924⟩
  rw [← get_eq_raw]
  exact (append (widen s22028_4 (by decide)) (append (widen s22032_16 (by decide)) (append (widen s22048_32 (by decide)) (append (widen s22080_64 (by decide)) (append (widen s22144_128 (by decide)) (append (widen s22272_256 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

private theorem s27648_512 : Run get 27648 512 ⟨384672084529,398356257037⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨360755563865,384635403626⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨360755563865,398356257037⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨360755563865,402326443510⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨312370152260,402326443510⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨326623210665,360698780395⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨282748408614,326546780316⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨282748408614,360698780395⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

theorem claim351 : CheckedClaim verifiedRow ⟨1,1,1,23888,29852,267477140723,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 23888 5965 ⟨267477159034,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s23888_16 (by decide)) (append (widen s23904_32 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_16 (by decide)) (append (widen s29840_8 (by decide)) (append (widen s29848_4 (by decide)) (widen s29852_1 (by decide))))))))))))

theorem claim352 : CheckedClaim verifiedRow ⟨1,1,1,23920,27896,273232485558,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 23920 3977 ⟨273232503869,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide))))))))))))

theorem claim353 : CheckedClaim verifiedRow ⟨1,1,1,23920,29884,264265940377,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 23920 5965 ⟨264265958688,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_32 (by decide)) (append (widen s29856_16 (by decide)) (append (widen s29872_8 (by decide)) (append (widen s29880_4 (by decide)) (widen s29884_1 (by decide))))))))))))

theorem claim354 : CheckedClaim verifiedRow ⟨1,1,1,23952,27928,275185348322,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 23952 3977 ⟨275185366633,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide)))))))))))

theorem claim355 : CheckedClaim verifiedRow ⟨1,1,1,23952,29916,261022094512,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 23952 5965 ⟨261022112823,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_64 (by decide)) (append (widen s29888_16 (by decide)) (append (widen s29904_8 (by decide)) (append (widen s29912_4 (by decide)) (widen s29916_1 (by decide)))))))))))))

theorem claim356 : CheckedClaim verifiedRow ⟨1,1,1,23984,25972,277135570529,379692369728⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 23984 1989 ⟨277135588840,379692351417⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_32 (by decide)) (append (widen s25952_16 (by decide)) (append (widen s25968_4 (by decide)) (widen s25972_1 (by decide)))))))))))

theorem claim357 : CheckedClaim verifiedRow ⟨1,1,1,23984,27960,277135570529,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 23984 3977 ⟨277135588840,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim358 : CheckedClaim verifiedRow ⟨1,1,1,24016,27992,279082864610,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 24016 3977 ⟨279082882921,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide)))))))))))

private theorem s29696_512 : Run get 29696 512 ⟨230084132469,282653728623⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨170035949245,229973521148⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨170035949245,282653728623⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨170035949245,360698780395⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨104402597734,169912560951⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨35287390025,104270276734⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨35287390025,169912560951⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim359 : CheckedClaim verifiedRow ⟨1,1,1,24016,31968,4399884783,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 24016 7953 ⟨4399903094,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim360 : CheckedClaim verifiedRow ⟨1,1,1,24946,27928,333006962440,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 24946 2983 ⟨333006980751,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s24946_2 (by decide)) (append (widen s24948_4 (by decide)) (append (widen s24952_8 (by decide)) (append (widen s24960_128 (by decide)) (append (widen s25088_512 (by decide)) (append (widen s25600_1024 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide))))))))))))

theorem claim361 : CheckedClaim verifiedRow ⟨1,1,1,25940,28922,345281126825,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 25940 2983 ⟨345281145136,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_128 (by decide)) (append (widen s28800_64 (by decide)) (append (widen s28864_32 (by decide)) (append (widen s28896_16 (by decide)) (append (widen s28912_8 (by decide)) (append (widen s28920_2 (by decide)) (widen s28922_1 (by decide))))))))))))))

theorem claim362 : CheckedClaim verifiedRow ⟨1,1,1,25940,29916,261022094512,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 25940 3977 ⟨261022112823,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_64 (by decide)) (append (widen s29888_16 (by decide)) (append (widen s29904_8 (by decide)) (append (widen s29912_4 (by decide)) (widen s29916_1 (by decide))))))))))))))

theorem claim363 : CheckedClaim verifiedRow ⟨1,1,1,25940,31904,13197368029,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 25940 5965 ⟨13197386340,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide))))))))))))

theorem claim364 : CheckedClaim verifiedRow ⟨1,1,1,25972,27960,379692333103,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 25972 1989 ⟨379692351414,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s25972_4 (by decide)) (append (widen s25976_8 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim365 : CheckedClaim verifiedRow ⟨1,1,1,26004,27992,380811784976,402326461821⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 26004 1989 ⟨380811803287,402326443510⟩
  rw [← get_eq_raw]
  exact (append (widen s26004_4 (by decide)) (append (widen s26008_8 (by decide)) (append (widen s26016_32 (by decide)) (append (widen s26048_64 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide))))))))))))

theorem claim366 : CheckedClaim verifiedRow ⟨1,1,1,27928,31904,13197368029,392101741679⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 27928 3977 ⟨13197386340,392101723368⟩
  rw [← get_eq_raw]
  exact (append (widen s27928_8 (by decide)) (append (widen s27936_32 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide)))))))))))

theorem claim367 : CheckedClaim verifiedRow ⟨1,1,1,27992,31968,4399884783,390250745945⟩ := by
  change Run (rawBlock verifiedRow 1 1 .first) 27992 3977 ⟨4399903094,390250727634⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
