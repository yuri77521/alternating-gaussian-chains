import Point22AtlasRangeGroup312Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf312

private abbrev get := fastBlock verifiedRow 3 1 .second
private theorem get_eq_raw : get = rawBlock verifiedRow 3 1 .second :=
  funext (fastBlock_eq_raw verifiedRow 3 1 .second)

private theorem s512_512 : Run get 512 512 ⟨-4334362281491,-4125815892292⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

private theorem s1024_512 : Run get 1024 512 ⟨-4125273149320,-3784243795954⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

private theorem s1536_512 : Run get 1536 512 ⟨-3783457923236,-3328581592379⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨-4125273149320,-3328581592379⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

theorem claim1011 : CheckedClaim verifiedRow ⟨3,1,2,96,2084,-4398258650920,-3291854242697⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 96 1989 ⟨-4398257845255,-3291855048362⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_32 (by decide)) (append (widen s2080_4 (by decide)) (widen s2084_1 (by decide)))))))))

private theorem s2048_512 : Run get 2048 512 ⟨-3327595123245,-2783156903795⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

private theorem s2560_512 : Run get 2560 512 ⟨-2782021757914,-2176148705531⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨-3327595123245,-2176148705531⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨-2174922382660,-1537561629449⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

theorem claim1012 : CheckedClaim verifiedRow ⟨3,1,2,96,4072,-4398258650920,-925578404444⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 96 3977 ⟨-4398257845255,-925579210109⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide))))))))))))))

private theorem s3584_512 : Run get 3584 512 ⟨-1536303163573,-897170913966⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨-2174922382660,-897170913966⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

private theorem s2048_2048 : Run get 2048 2048 ⟨-3327595123245,-897170913966⟩ :=
  join s2048_1024 s3072_1024 (by decide) (by decide)

theorem claim1013 : CheckedClaim verifiedRow ⟨3,1,2,160,4136,-4394775893612,-846661649098⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 160 3977 ⟨-4394775087947,-846662454763⟩
  rw [← get_eq_raw]
  exact (append (widen s160_32 (by decide)) (append (widen s192_64 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_32 (by decide)) (append (widen s4128_8 (by decide)) (widen s4136_1 (by decide))))))))))

theorem claim1014 : CheckedClaim verifiedRow ⟨3,1,2,2084,4072,-3291855854036,-925578404444⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 2084 1989 ⟨-3291855048371,-925579210109⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide)))))))))))))))

private theorem s4096_512 : Run get 4096 512 ⟨-895936950690,-282616841907⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

theorem claim1015 : CheckedClaim verifiedRow ⟨3,1,2,4072,5066,-925580015783,226640526933⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 4072 995 ⟨-925579210118,226639721268⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_64 (by decide)) (append (widen s5056_8 (by decide)) (append (widen s5064_2 (by decide)) (widen s5066_1 (by decide))))))))))

private theorem s4608_512 : Run get 4608 512 ⟨-281458168590,282198432990⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨-895936950690,282198432990⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨283239641496,778299242964⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

theorem claim1016 : CheckedClaim verifiedRow ⟨3,1,2,4072,6060,-925580015783,1131180715557⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 4072 1989 ⟨-925579210118,1131179909892⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))

private theorem s5632_512 : Run get 5632 512 ⟨779191289696,1192346712974⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨283239641496,1192346712974⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨-895936950690,1192346712974⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨1193069282556,1516859245249⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨1517403371595,1749978977867⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨1193069282556,1749978977867⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨1750346187238,1894858633774⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim1017 : CheckedClaim verifiedRow ⟨3,1,2,4072,8048,-925580015783,1948518186867⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 4072 3977 ⟨-925579210118,1948517381202⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim1018 : CheckedClaim verifiedRow ⟨3,1,2,4104,8080,-886069664965,1951304780839⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 4104 3977 ⟨-886068859300,1951303975174⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide)))))))))))))))

private theorem s8192_512 : Run get 8192 512 ⟨1952043518422,1963903245186⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

private theorem s8704_512 : Run get 8704 512 ⟨1886962592682,1951969074874⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨1886962592682,1963903245186⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨1776694168570,1886786933353⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

private theorem s9728_512 : Run get 9728 512 ⟨1634354128770,1776443238926⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨1634354128770,1886786933353⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨1634354128770,1963903245186⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨1472251110481,1634052968655⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨1301341153712,1471922578829⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨1301341153712,1634052968655⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨1130897078059,1301005075674⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

theorem claim1019 : CheckedClaim verifiedRow ⟨3,1,2,8048,12024,1050476653116,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 8048 3977 ⟨1050477458781,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))

theorem claim1020 : CheckedClaim verifiedRow ⟨3,1,2,8080,10068,1684675875750,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 8080 1989 ⟨1684676681415,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_64 (by decide)) (append (widen s10048_16 (by decide)) (append (widen s10064_4 (by decide)) (widen s10068_1 (by decide)))))))))))

theorem claim1021 : CheckedClaim verifiedRow ⟨3,1,2,8080,12056,1040316731142,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 8080 3977 ⟨1040317536807,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

private theorem s11776_512 : Run get 11776 512 ⟨968376902920,1130569801889⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨968376902920,1301005075674⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨968376902920,1634052968655⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨968376902920,1963903245186⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨819460900443,968071219722⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨688217890817,819186256732⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨688217890817,968071219722⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨577357750748,687980811807⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

private theorem s13824_512 : Run get 13824 512 ⟨488527875001,577162389818⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨488527875001,687980811807⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨488527875001,968071219722⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨422615307244,488376609843⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨380022215828,422509313316⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨380022215828,488376609843⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨360889278182,379961960554⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim1022 : CheckedClaim verifiedRow ⟨3,1,2,8080,16032,359726859971,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 8080 7953 ⟨359727665636,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim1023 : CheckedClaim verifiedRow ⟨3,1,2,8112,16064,359726859971,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 8112 7953 ⟨359727665636,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim1024 : CheckedClaim verifiedRow ⟨3,1,2,9042,10036,1693813542836,1914672508175⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 9042 995 ⟨1693814348501,1914671702510⟩
  rw [← get_eq_raw]
  exact (append (widen s9042_2 (by decide)) (append (widen s9044_4 (by decide)) (append (widen s9048_8 (by decide)) (append (widen s9056_32 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))))

theorem claim1025 : CheckedClaim verifiedRow ⟨3,1,2,10036,11030,1379576069142,1693815154175⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 10036 995 ⟨1379576874807,1693814348510⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_256 (by decide)) (append (widen s11008_16 (by decide)) (append (widen s11024_4 (by decide)) (append (widen s11028_2 (by decide)) (widen s11030_1 (by decide)))))))))))

theorem claim1026 : CheckedClaim verifiedRow ⟨3,1,2,10036,12024,1050476653116,1693815154175⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 10036 1989 ⟨1050477458781,1693814348510⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim1027 : CheckedClaim verifiedRow ⟨3,1,2,10068,11062,1368853700480,1684677487089⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 10068 995 ⟨1368854506145,1684676681424⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_256 (by decide)) (append (widen s11008_32 (by decide)) (append (widen s11040_16 (by decide)) (append (widen s11056_4 (by decide)) (append (widen s11060_2 (by decide)) (widen s11062_1 (by decide))))))))))))

theorem claim1028 : CheckedClaim verifiedRow ⟨3,1,2,11030,12024,1050476653116,1379577680481⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 11030 995 ⟨1050477458781,1379576874816⟩
  rw [← get_eq_raw]
  exact (append (widen s11030_2 (by decide)) (append (widen s11032_8 (by decide)) (append (widen s11040_32 (by decide)) (append (widen s11072_64 (by decide)) (append (widen s11136_128 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim1029 : CheckedClaim verifiedRow ⟨3,1,2,12024,13018,760974199205,1050478264455⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 12024 995 ⟨760975004870,1050477458790⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_64 (by decide)) (append (widen s12992_16 (by decide)) (append (widen s13008_8 (by decide)) (append (widen s13016_2 (by decide)) (widen s13018_1 (by decide))))))))))

theorem claim1030 : CheckedClaim verifiedRow ⟨3,1,2,12024,14012,541940470156,1050478264455⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 12024 1989 ⟨541941275821,1050477458790⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide)))))))))))

theorem claim1031 : CheckedClaim verifiedRow ⟨3,1,2,12024,16000,359772749358,1050478264455⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 12024 3977 ⟨359773555023,1050477458790⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim1032 : CheckedClaim verifiedRow ⟨3,1,2,12056,13050,752715284745,1040318342481⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 12056 995 ⟨752716090410,1040317536816⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_64 (by decide)) (append (widen s12992_32 (by decide)) (append (widen s13024_16 (by decide)) (append (widen s13040_8 (by decide)) (append (widen s13048_2 (by decide)) (widen s13050_1 (by decide)))))))))))))

theorem claim1033 : CheckedClaim verifiedRow ⟨3,1,2,12056,14044,536245946050,1040318342481⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 12056 1989 ⟨536246751715,1040317536816⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide)))))))))))))

theorem claim1034 : CheckedClaim verifiedRow ⟨3,1,2,12056,16032,359726859971,1040318342481⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 12056 3977 ⟨359727665636,1040317536816⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim1035 : CheckedClaim verifiedRow ⟨3,1,2,12088,16064,359726859971,1030202934652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 12088 3977 ⟨359727665636,1030202128987⟩
  rw [← get_eq_raw]
  exact (append (widen s12088_8 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim1036 : CheckedClaim verifiedRow ⟨3,1,2,14012,16000,359772749358,541942081495⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 14012 1989 ⟨359773555023,541941275830⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim1037 : CheckedClaim verifiedRow ⟨3,1,2,14044,16032,359726859971,536247557389⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 14044 1989 ⟨359727665636,536246751724⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))

private theorem s16384_512 : Run get 16384 512 ⟨365280096815,393094564424⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨393171909247,444367615961⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨365280096815,444367615961⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨444490581212,518851956241⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

theorem claim1038 : CheckedClaim verifiedRow ⟨3,1,2,16000,17988,359726859971,530641087026⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 16000 1989 ⟨359727665636,530640281361⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide))))))))

private theorem s17920_512 : Run get 17920 512 ⟨519019861196,615994799204⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨444490581212,615994799204⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨365280096815,615994799204⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨616206083018,734661132359⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨734912824575,872845003948⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨616206083018,872845003948⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

private theorem s19456_512 : Run get 19456 512 ⟨873132135230,1027365376226⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

theorem claim1039 : CheckedClaim verifiedRow ⟨3,1,2,16000,19976,359726859971,1030202934652⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 16000 3977 ⟨359727665636,1030202128987⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))

theorem claim1040 : CheckedClaim verifiedRow ⟨3,1,2,16032,18020,359726859971,536247557389⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 16032 1989 ⟨359727665636,536246751724⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))

theorem claim1041 : CheckedClaim verifiedRow ⟨3,1,2,16032,20008,359726859971,1040318342481⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 16032 3977 ⟨359727665636,1040317536816⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))

private theorem s19968_512 : Run get 19968 512 ⟨1027680390889,1193581239917⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨873132135230,1193581239917⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨616206083018,1193581239917⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨365280096815,1193581239917⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨1193913483835,1365166043872⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨1365501409852,1533984426603⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨1193913483835,1533984426603⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

private theorem s21504_512 : Run get 21504 512 ⟨1534305241876,1690113501162⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨1690398735802,1822045410377⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨1534305241876,1822045410377⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨1193913483835,1822045410377⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨1822271269381,1917096768659⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨1917237703098,1962033792508⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨1822271269381,1962033792508⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

theorem claim1042 : CheckedClaim verifiedRow ⟨3,1,2,16032,23984,359726859971,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 16032 7953 ⟨359727665636,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))

theorem claim1043 : CheckedClaim verifiedRow ⟨3,1,2,16064,20040,359772749358,1050478264455⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 16064 3977 ⟨359773555023,1050477458790⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide)))))))))

theorem claim1044 : CheckedClaim verifiedRow ⟨3,1,2,16064,24016,359772749358,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 16064 7953 ⟨359773555023,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))

theorem claim1045 : CheckedClaim verifiedRow ⟨3,1,2,17026,18020,403986977107,536247557389⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 17026 995 ⟨403987782772,536246751724⟩
  rw [← get_eq_raw]
  exact (append (widen s17026_2 (by decide)) (append (widen s17028_4 (by decide)) (append (widen s17032_8 (by decide)) (append (widen s17040_16 (by decide)) (append (widen s17056_32 (by decide)) (append (widen s17088_64 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide)))))))))))))

theorem claim1046 : CheckedClaim verifiedRow ⟨3,1,2,18020,20008,536245946050,1040318342481⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 18020 1989 ⟨536246751715,1040317536816⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim1047 : CheckedClaim verifiedRow ⟨3,1,2,18052,20040,541940470156,1050478264455⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 18052 1989 ⟨541941275821,1050477458790⟩
  rw [← get_eq_raw]
  exact (append (widen s18052_4 (by decide)) (append (widen s18056_8 (by decide)) (append (widen s18064_16 (by decide)) (append (widen s18080_32 (by decide)) (append (widen s18112_64 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide))))))))))))

theorem claim1048 : CheckedClaim verifiedRow ⟨3,1,2,19014,20008,752715284745,1040318342481⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 19014 995 ⟨752716090410,1040317536816⟩
  rw [← get_eq_raw]
  exact (append (widen s19014_2 (by decide)) (append (widen s19016_8 (by decide)) (append (widen s19024_16 (by decide)) (append (widen s19040_32 (by decide)) (append (widen s19072_128 (by decide)) (append (widen s19200_256 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim1049 : CheckedClaim verifiedRow ⟨3,1,2,20008,23984,1040316731142,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 20008 3977 ⟨1040317536807,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide)))))))))))))

theorem claim1050 : CheckedClaim verifiedRow ⟨3,1,2,20040,22028,1050476653116,1693815154175⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 20040 1989 ⟨1050477458781,1693814348510⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_512 (by decide)) (append (widen s22016_8 (by decide)) (append (widen s22024_4 (by decide)) (widen s22028_1 (by decide)))))))))))

theorem claim1051 : CheckedClaim verifiedRow ⟨3,1,2,20040,24016,1050476653116,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 20040 3977 ⟨1050477458781,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim1052 : CheckedClaim verifiedRow ⟨3,1,2,21002,21996,1368853700480,1684677487089⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 21002 995 ⟨1368854506145,1684676681424⟩
  rw [← get_eq_raw]
  exact (append (widen s21002_2 (by decide)) (append (widen s21004_4 (by decide)) (append (widen s21008_16 (by decide)) (append (widen s21024_32 (by decide)) (append (widen s21056_64 (by decide)) (append (widen s21120_128 (by decide)) (append (widen s21248_256 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide)))))))))))))))

theorem claim1053 : CheckedClaim verifiedRow ⟨3,1,2,21996,23984,1684675875750,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 21996 1989 ⟨1684676681415,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s21996_4 (by decide)) (append (widen s22000_16 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))

theorem claim1054 : CheckedClaim verifiedRow ⟨3,1,2,22028,24016,1693813542836,1963904050851⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 22028 1989 ⟨1693814348501,1963903245186⟩
  rw [← get_eq_raw]
  exact (append (widen s22028_4 (by decide)) (append (widen s22032_16 (by decide)) (append (widen s22048_32 (by decide)) (append (widen s22080_64 (by decide)) (append (widen s22144_128 (by decide)) (append (widen s22272_256 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

private theorem s24064_512 : Run get 24064 512 ⟨1851008713863,1943795002937⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨1674034349923,1850747554127⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨1407116992507,1673601929400⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨1407116992507,1850747554127⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

theorem claim1055 : CheckedClaim verifiedRow ⟨3,1,2,23952,25940,1178551887257,1953805195621⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 23952 1989 ⟨1178552692922,1953804389956⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_16 (by decide)) (append (widen s25936_4 (by decide)) (widen s25940_1 (by decide)))))))))))

theorem claim1056 : CheckedClaim verifiedRow ⟨3,1,2,23984,25972,1155040346543,1951304780839⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 23984 1989 ⟨1155041152208,1951303975174⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_32 (by decide)) (append (widen s25952_16 (by decide)) (append (widen s25968_4 (by decide)) (widen s25972_1 (by decide)))))))))))

private theorem s25600_512 : Run get 25600 512 ⟨1048871701620,1406505942373⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨603189990712,1048084263986⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨603189990712,1406505942373⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨603189990712,1850747554127⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨79722749629,602239306138⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨-506047834647,78633424057⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨-506047834647,602239306138⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

theorem claim1057 : CheckedClaim verifiedRow ⟨3,1,2,23984,27960,-886069664965,1951304780839⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 23984 3977 ⟨-886068859300,1951303975174⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim1058 : CheckedClaim verifiedRow ⟨3,1,2,24016,27992,-925580015783,1948518186867⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 24016 3977 ⟨-925579210118,1948517381202⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide)))))))))))

private theorem s27648_512 : Run get 27648 512 ⟨-1133208743398,-507240037940⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨-1776307928041,-1134458168334⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨-1776307928041,-507240037940⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨-1776307928041,602239306138⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨-1776307928041,1850747554127⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨-2406706721676,-1777561236698⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨-2994310759253,-2407905940926⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨-2994310759253,-1777561236698⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

private theorem s29696_512 : Run get 29696 512 ⟨-3509550607704,-2995396954454⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨-3925447613719,-3510467892406⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨-3925447613719,-2995396954454⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨-3925447613719,-1777561236698⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨-4219581120097,-3926147149147⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨-4375773652559,-4220024738988⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨-4375773652559,-3926147149147⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim1059 : CheckedClaim verifiedRow ⟨3,1,2,24016,31968,-4398258650920,1948518186867⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 24016 7953 ⟨-4398257845255,1948517381202⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim1060 : CheckedClaim verifiedRow ⟨3,1,2,25940,27928,-846663260437,1178553498596⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 25940 1989 ⟨-846662454772,1178552692931⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide)))))))))))

theorem claim1061 : CheckedClaim verifiedRow ⟨3,1,2,25972,27960,-886069664965,1155041957882⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 25972 1989 ⟨-886068859300,1155041152217⟩
  rw [← get_eq_raw]
  exact (append (widen s25972_4 (by decide)) (append (widen s25976_8 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim1062 : CheckedClaim verifiedRow ⟨3,1,2,26004,27992,-925580015783,1131180715557⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 26004 1989 ⟨-925579210118,1131179909892⟩
  rw [← get_eq_raw]
  exact (append (widen s26004_4 (by decide)) (append (widen s26008_8 (by decide)) (append (widen s26016_32 (by decide)) (append (widen s26048_64 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide))))))))))))

theorem claim1063 : CheckedClaim verifiedRow ⟨3,1,2,27928,31904,-4394775893612,-846661649098⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 27928 3977 ⟨-4394775087947,-846662454763⟩
  rw [← get_eq_raw]
  exact (append (widen s27928_8 (by decide)) (append (widen s27936_32 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide)))))))))))

theorem claim1064 : CheckedClaim verifiedRow ⟨3,1,2,27992,31968,-4398258650920,-925578404444⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 27992 3977 ⟨-4398257845255,-925579210109⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim1065 : CheckedClaim verifiedRow ⟨3,1,2,29980,31968,-4398258650920,-3291854242697⟩ := by
  change Run (rawBlock verifiedRow 3 1 .second) 29980 1989 ⟨-4398257845255,-3291855048362⟩
  rw [← get_eq_raw]
  exact (append (widen s29980_4 (by decide)) (append (widen s29984_32 (by decide)) (append (widen s30016_64 (by decide)) (append (widen s30080_128 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
