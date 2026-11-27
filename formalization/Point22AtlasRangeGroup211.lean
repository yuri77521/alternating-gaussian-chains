import Point22AtlasRangeGroup211Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf211

private abbrev get := fastBlock verifiedRow 2 1 .first
private theorem get_eq_raw : get = rawBlock verifiedRow 2 1 .first :=
  funext (fastBlock_eq_raw verifiedRow 2 1 .first)

private theorem s512_512 : Run get 512 512 ⟨-4330514255,-4117568518⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

theorem claim639 : CheckedClaim verifiedRow ⟨2,1,1,64,1058,-4399358952,-4097946767⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 64 995 ⟨-4399322330,-4097983389⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_32 (by decide)) (append (widen s1056_2 (by decide)) (widen s1058_1 (by decide))))))))

private theorem s1024_512 : Run get 1024 512 ⟨-4117017542,-3772043877⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

private theorem s1536_512 : Run get 1536 512 ⟨-3771250877,-3313091132⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨-4117017542,-3313091132⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

theorem claim640 : CheckedClaim verifiedRow ⟨2,1,1,64,2052,-4399358952,-3308090424⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 64 1989 ⟨-4399322330,-3308127046⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide))))))))

private theorem s2048_512 : Run get 2048 512 ⟨-3312099001,-2765194120⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

private theorem s2560_512 : Run get 2560 512 ⟨-2764055025,-2156627822⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨-3312099001,-2156627822⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨-2155399388,-1517428214⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

theorem claim641 : CheckedClaim verifiedRow ⟨2,1,1,64,4040,-4399358952,-945244284⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 64 3977 ⟨-4399322330,-945280906⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))

theorem claim642 : CheckedClaim verifiedRow ⟨2,1,1,1058,2052,-4098020017,-3308090424⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 1058 995 ⟨-4097983395,-3308127046⟩
  rw [← get_eq_raw]
  exact (append (widen s1058_2 (by decide)) (append (widen s1060_4 (by decide)) (append (widen s1064_8 (by decide)) (append (widen s1072_16 (by decide)) (append (widen s1088_64 (by decide)) (append (widen s1152_128 (by decide)) (append (widen s1280_256 (by decide)) (append (widen s1536_512 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide)))))))))))

theorem claim643 : CheckedClaim verifiedRow ⟨2,1,1,2052,4040,-3308163674,-945244284⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 2052 1989 ⟨-3308127052,-945280906⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))))

theorem claim644 : CheckedClaim verifiedRow ⟨2,1,1,2084,4072,-3276193608,-905678200⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 2084 1989 ⟨-3276156986,-905714822⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide)))))))))))))))

private theorem s3584_512 : Run get 3584 512 ⟨-1516169472,-877338599⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨-2155399388,-877338599⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

theorem claim645 : CheckedClaim verifiedRow ⟨2,1,1,2116,4104,-3243882490,-866212928⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 2116 1989 ⟨-3243845868,-866249550⟩
  rw [← get_eq_raw]
  exact (append (widen s2116_4 (by decide)) (append (widen s2120_8 (by decide)) (append (widen s2128_16 (by decide)) (append (widen s2144_32 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_8 (by decide)) (widen s4104_1 (by decide)))))))))))

theorem claim646 : CheckedClaim verifiedRow ⟨2,1,1,3046,4040,-2187336927,-945244284⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 3046 995 ⟨-2187300305,-945280906⟩
  rw [← get_eq_raw]
  exact (append (widen s3046_2 (by decide)) (append (widen s3048_8 (by decide)) (append (widen s3056_16 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide))))))))))

private theorem s4096_512 : Run get 4096 512 ⟨-876106074,-263910786⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

theorem claim647 : CheckedClaim verifiedRow ⟨2,1,1,4040,5034,-945317534,210011659⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4040 995 ⟨-945280912,209975037⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_32 (by decide)) (append (widen s5024_8 (by decide)) (append (widen s5032_2 (by decide)) (widen s5034_1 (by decide)))))))))))

private theorem s4608_512 : Run get 4608 512 ⟨-262755045,299086999⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨-876106074,299086999⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨300124079,792844452⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

theorem claim648 : CheckedClaim verifiedRow ⟨2,1,1,4040,6028,-945317534,1119488498⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4040 1989 ⟨-945280912,1119451876⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide)))))))))))

private theorem s5632_512 : Run get 5632 512 ⟨793731520,1204204146⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨300124079,1204204146⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨-876106074,1204204146⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨1204921243,1525866908⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨1526405418,1756144834⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨1204921243,1756144834⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨1756506595,1898337414⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim649 : CheckedClaim verifiedRow ⟨2,1,1,4040,8016,-945317534,1947330706⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4040 3977 ⟨-945280912,1947294084⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim650 : CheckedClaim verifiedRow ⟨2,1,1,4072,6060,-905751450,1143525393⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4072 1989 ⟨-905714828,1143488771⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))

theorem claim651 : CheckedClaim verifiedRow ⟨2,1,1,4072,8048,-905751450,1950258832⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4072 3977 ⟨-905714828,1950222210⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim652 : CheckedClaim verifiedRow ⟨2,1,1,4104,6092,-866286178,1167213142⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4104 1989 ⟨-866249556,1167176520⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_64 (by decide)) (append (widen s6080_8 (by decide)) (append (widen s6088_4 (by decide)) (widen s6092_1 (by decide)))))))))))))))

theorem claim653 : CheckedClaim verifiedRow ⟨2,1,1,4104,8080,-866286178,1952899389⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4104 3977 ⟨-866249556,1952862767⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide)))))))))))))))

theorem claim654 : CheckedClaim verifiedRow ⟨2,1,1,4136,8112,-826928084,1955255100⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 4136 3977 ⟨-826891462,1955218478⟩
  rw [← get_eq_raw]
  exact (append (widen s4136_8 (by decide)) (append (widen s4144_16 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_16 (by decide)) (widen s8112_1 (by decide)))))))))))))))

theorem claim655 : CheckedClaim verifiedRow ⟨2,1,1,5034,6028,209938409,1119488498⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 5034 995 ⟨209975031,1119451876⟩
  rw [← get_eq_raw]
  exact (append (widen s5034_2 (by decide)) (append (widen s5036_4 (by decide)) (append (widen s5040_16 (by decide)) (append (widen s5056_64 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide)))))))))))

theorem claim656 : CheckedClaim verifiedRow ⟨2,1,1,5066,6060,243707203,1143525393⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 5066 995 ⟨243743825,1143488771⟩
  rw [← get_eq_raw]
  exact (append (widen s5066_2 (by decide)) (append (widen s5068_4 (by decide)) (append (widen s5072_16 (by decide)) (append (widen s5088_32 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide))))))))))))

theorem claim657 : CheckedClaim verifiedRow ⟨2,1,1,6028,8016,1119415248,1947330706⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 6028 1989 ⟨1119451870,1947294084⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim658 : CheckedClaim verifiedRow ⟨2,1,1,6060,8048,1143452143,1950258832⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 6060 1989 ⟨1143488765,1950222210⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim659 : CheckedClaim verifiedRow ⟨2,1,1,6092,8080,1167139892,1952899389⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 6092 1989 ⟨1167176514,1952862767⟩
  rw [← get_eq_raw]
  exact (append (widen s6092_4 (by decide)) (append (widen s6096_16 (by decide)) (append (widen s6112_32 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide))))))))))

theorem claim660 : CheckedClaim verifiedRow ⟨2,1,1,6124,8112,1190477238,1955255100⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 6124 1989 ⟨1190513860,1955218478⟩
  rw [← get_eq_raw]
  exact (append (widen s6124_4 (by decide)) (append (widen s6128_16 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_16 (by decide)) (widen s8112_1 (by decide))))))))))

private theorem s8192_512 : Run get 8192 512 ⟨1951042952,1964150939⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

theorem claim661 : CheckedClaim verifiedRow ⟨2,1,1,8016,9010,1917106606,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8016 995 ⟨1917143228,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_512 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_32 (by decide)) (append (widen s8992_16 (by decide)) (append (widen s9008_2 (by decide)) (widen s9010_1 (by decide))))))))))

private theorem s8704_512 : Run get 8704 512 ⟨1884298997,1950964866⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨1884298997,1964150939⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨1772782989,1884120502⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

theorem claim662 : CheckedClaim verifiedRow ⟨2,1,1,8016,10004,1698403780,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8016 1989 ⟨1698440402,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide))))))))))

private theorem s9728_512 : Run get 9728 512 ⟨1629598791,1772530032⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨1629598791,1884120502⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨1629598791,1964150939⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨1467021912,1629296364⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨1295960909,1466692794⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨1295960909,1629296364⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨1125633376,1295624823⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

theorem claim663 : CheckedClaim verifiedRow ⟨2,1,1,8016,11992,1055496360,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8016 3977 ⟨1055532982,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))

theorem claim664 : CheckedClaim verifiedRow ⟨2,1,1,8048,10036,1689310543,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8048 1989 ⟨1689347165,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))

theorem claim665 : CheckedClaim verifiedRow ⟨2,1,1,8048,12024,1045313364,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8048 3977 ⟨1045349986,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))

theorem claim666 : CheckedClaim verifiedRow ⟨2,1,1,8080,10068,1680123473,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8080 1989 ⟨1680160095,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_64 (by decide)) (append (widen s10048_16 (by decide)) (append (widen s10064_4 (by decide)) (widen s10068_1 (by decide)))))))))))

theorem claim667 : CheckedClaim verifiedRow ⟨2,1,1,8080,12056,1035174226,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8080 3977 ⟨1035210848,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

private theorem s11776_512 : Run get 11776 512 ⟨963440266,1125306558⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨963440266,1295624823⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨963440266,1629296364⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨963440266,1964150939⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨815007768,963135398⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨684357112,814734196⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨684357112,963135398⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨574159237,684121276⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

private theorem s13824_512 : Run get 13824 512 ⟨486032128,573965224⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨486032128,684121276⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨486032128,963135398⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨420842683,485882267⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨378981010,420738119⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨378981010,485882267⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨360581917,378922193⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim668 : CheckedClaim verifiedRow ⟨2,1,1,8080,16032,359603086,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8080 7953 ⟨359639708,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim669 : CheckedClaim verifiedRow ⟨2,1,1,8112,12088,1025080302,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8112 3977 ⟨1025116924,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_32 (by decide)) (append (widen s12064_16 (by decide)) (append (widen s12080_8 (by decide)) (widen s12088_1 (by decide)))))))))))

theorem claim670 : CheckedClaim verifiedRow ⟨2,1,1,8112,16064,359603086,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 8112 7953 ⟨359639708,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim671 : CheckedClaim verifiedRow ⟨2,1,1,10004,11992,1055496360,1698477030⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 10004 1989 ⟨1055532982,1698440408⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide)))))))))))))

theorem claim672 : CheckedClaim verifiedRow ⟨2,1,1,10036,12024,1045313364,1689383793⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 10036 1989 ⟨1045349986,1689347171⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim673 : CheckedClaim verifiedRow ⟨2,1,1,10068,12056,1035174226,1680196723⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 10068 1989 ⟨1035210848,1680160101⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

theorem claim674 : CheckedClaim verifiedRow ⟨2,1,1,11992,13980,544700794,1055569610⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 11992 1989 ⟨544737416,1055532988⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide)))))))))))

theorem claim675 : CheckedClaim verifiedRow ⟨2,1,1,11992,15968,359706337,1055569610⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 11992 3977 ⟨359742959,1055532988⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim676 : CheckedClaim verifiedRow ⟨2,1,1,12024,14012,538962107,1045386614⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 12024 1989 ⟨538998729,1045349992⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide)))))))))))

theorem claim677 : CheckedClaim verifiedRow ⟨2,1,1,12024,16000,359614558,1045386614⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 12024 3977 ⟨359651180,1045349992⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim678 : CheckedClaim verifiedRow ⟨2,1,1,12056,14044,533311374,1035247476⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 12056 1989 ⟨533347996,1035210854⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide)))))))))))))

theorem claim679 : CheckedClaim verifiedRow ⟨2,1,1,12056,16032,359603086,1035247476⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 12056 3977 ⟨359639708,1035210854⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim680 : CheckedClaim verifiedRow ⟨2,1,1,12088,16064,359603086,1025153552⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 12088 3977 ⟨359639708,1025116930⟩
  rw [← get_eq_raw]
  exact (append (widen s12088_8 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim681 : CheckedClaim verifiedRow ⟨2,1,1,13980,15968,359706337,544774044⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 13980 1989 ⟨359742959,544737422⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim682 : CheckedClaim verifiedRow ⟨2,1,1,14012,16000,359614558,539035357⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 14012 1989 ⟨359651180,538998735⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim683 : CheckedClaim verifiedRow ⟨2,1,1,14044,16032,359603086,533384624⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 14044 1989 ⟨359639708,533348002⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))

theorem claim684 : CheckedClaim verifiedRow ⟨2,1,1,14076,16064,359603086,527822061⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 14076 1989 ⟨359639708,527785439⟩
  rw [← get_eq_raw]
  exact (append (widen s14076_4 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))

private theorem s16384_512 : Run get 16384 512 ⟨365708378,394255080⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨394333850,446258741⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨365708378,446258741⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨446383121,521463911⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

theorem claim685 : CheckedClaim verifiedRow ⟨2,1,1,15968,17956,359603086,527822061⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 15968 1989 ⟨359639708,527785439⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide)))))))))

private theorem s17920_512 : Run get 17920 512 ⟨521633201,619304542⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨446383121,619304542⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨365708378,619304542⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨619517148,738624028⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨738876927,877385442⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨619517148,877385442⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

theorem claim686 : CheckedClaim verifiedRow ⟨2,1,1,15968,19944,359603086,1025153552⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 15968 3977 ⟨359639708,1025116930⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))

theorem claim687 : CheckedClaim verifiedRow ⟨2,1,1,16000,17988,359603086,533384624⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 16000 1989 ⟨359639708,533348002⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide))))))))

private theorem s19456_512 : Run get 19456 512 ⟨877673596,1032367309⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

theorem claim688 : CheckedClaim verifiedRow ⟨2,1,1,16000,19976,359603086,1035247476⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 16000 3977 ⟨359639708,1035210854⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))

theorem claim689 : CheckedClaim verifiedRow ⟨2,1,1,16032,18020,359614558,539035357⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 16032 1989 ⟨359651180,538998735⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))

theorem claim690 : CheckedClaim verifiedRow ⟨2,1,1,16032,20008,359614558,1045386614⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 16032 3977 ⟨359651180,1045349992⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))

private theorem s19968_512 : Run get 19968 512 ⟨1032683075,1198879791⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨877673596,1198879791⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨619517148,1198879791⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨365708378,1198879791⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨1199212412,1370541489⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨1370876746,1539159915⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨1199212412,1539159915⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

private theorem s21504_512 : Run get 21504 512 ⟨1539480027,1694757788⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨1695041624,1825781643⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨1539480027,1825781643⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨1199212412,1825781643⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨1826005331,1919517950⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨1919655901,1962724947⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨1826005331,1962724947⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

theorem claim691 : CheckedClaim verifiedRow ⟨2,1,1,16032,23984,359614558,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 16032 7953 ⟨359651180,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))

theorem claim692 : CheckedClaim verifiedRow ⟨2,1,1,16064,20040,359706337,1055569610⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 16064 3977 ⟨359742959,1055532988⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide)))))))))

theorem claim693 : CheckedClaim verifiedRow ⟨2,1,1,16064,24016,359706337,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 16064 7953 ⟨359742959,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))

theorem claim694 : CheckedClaim verifiedRow ⟨2,1,1,17956,19944,527748811,1025153552⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 17956 1989 ⟨527785433,1025116930⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))

theorem claim695 : CheckedClaim verifiedRow ⟨2,1,1,17988,19976,533311374,1035247476⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 17988 1989 ⟨533347996,1035210854⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide)))))))))))

theorem claim696 : CheckedClaim verifiedRow ⟨2,1,1,18020,20008,538962107,1045386614⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 18020 1989 ⟨538998729,1045349992⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim697 : CheckedClaim verifiedRow ⟨2,1,1,19944,21932,1025080302,1670918797⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 19944 1989 ⟨1025116924,1670882175⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_32 (by decide)) (append (widen s21920_8 (by decide)) (append (widen s21928_4 (by decide)) (widen s21932_1 (by decide)))))))))))

theorem claim698 : CheckedClaim verifiedRow ⟨2,1,1,19944,23920,1025080302,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 19944 3977 ⟨1025116924,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))

theorem claim699 : CheckedClaim verifiedRow ⟨2,1,1,19976,21964,1035174226,1680196723⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 19976 1989 ⟨1035210848,1680160101⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide))))))))))))))

theorem claim700 : CheckedClaim verifiedRow ⟨2,1,1,19976,23952,1035174226,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 19976 3977 ⟨1035210848,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide)))))))))))))

theorem claim701 : CheckedClaim verifiedRow ⟨2,1,1,20008,21996,1045313364,1689383793⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 20008 1989 ⟨1045349986,1689347171⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide))))))))))))))

theorem claim702 : CheckedClaim verifiedRow ⟨2,1,1,20008,23984,1045313364,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 20008 3977 ⟨1045349986,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide)))))))))))))

theorem claim703 : CheckedClaim verifiedRow ⟨2,1,1,20040,24016,1055496360,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 20040 3977 ⟨1055532982,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim704 : CheckedClaim verifiedRow ⟨2,1,1,21932,23920,1670845547,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 21932 1989 ⟨1670882169,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s21932_4 (by decide)) (append (widen s21936_16 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))

theorem claim705 : CheckedClaim verifiedRow ⟨2,1,1,21964,23952,1680123473,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 21964 1989 ⟨1680160095,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s21964_4 (by decide)) (append (widen s21968_16 (by decide)) (append (widen s21984_32 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide))))))))))

theorem claim706 : CheckedClaim verifiedRow ⟨2,1,1,21996,23984,1689310543,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 21996 1989 ⟨1689347165,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s21996_4 (by decide)) (append (widen s22000_16 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))

theorem claim707 : CheckedClaim verifiedRow ⟨2,1,1,22028,24016,1698403780,1964187561⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 22028 1989 ⟨1698440402,1964150939⟩
  rw [← get_eq_raw]
  exact (append (widen s22028_4 (by decide)) (append (widen s22032_16 (by decide)) (append (widen s22048_32 (by decide)) (append (widen s22080_64 (by decide)) (append (widen s22144_128 (by decide)) (append (widen s22272_256 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

private theorem s24064_512 : Run get 24064 512 ⟨1847108301,1942356844⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨1667412864,1846842047⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨1397641663,1666974959⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨1397641663,1846842047⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

theorem claim708 : CheckedClaim verifiedRow ⟨2,1,1,23920,25908,1190477238,1955255100⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 23920 1989 ⟨1190513860,1955218478⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_32 (by decide)) (append (widen s25888_16 (by decide)) (append (widen s25904_4 (by decide)) (widen s25908_1 (by decide))))))))))

theorem claim709 : CheckedClaim verifiedRow ⟨2,1,1,23952,25940,1167139892,1952899389⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 23952 1989 ⟨1167176514,1952862767⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_16 (by decide)) (append (widen s25936_4 (by decide)) (widen s25940_1 (by decide)))))))))))

theorem claim710 : CheckedClaim verifiedRow ⟨2,1,1,23984,25972,1143452143,1950258832⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 23984 1989 ⟨1143488765,1950222210⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_32 (by decide)) (append (widen s25952_16 (by decide)) (append (widen s25968_4 (by decide)) (widen s25972_1 (by decide)))))))))))

private theorem s25600_512 : Run get 25600 512 ⟨1036560899,1397025009⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨588234889,1035768058⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨588234889,1397025009⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨588234889,1846842047⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨62497764,587279351⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨-524988406,61404496⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨-524988406,587279351⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

theorem claim711 : CheckedClaim verifiedRow ⟨2,1,1,23984,27960,-905751450,1950258832⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 23984 3977 ⟨-905714828,1950222210⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim712 : CheckedClaim verifiedRow ⟨2,1,1,24016,26004,1119415248,1947330706⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 24016 1989 ⟨1119451870,1947294084⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_128 (by decide)) (append (widen s25984_16 (by decide)) (append (widen s26000_4 (by decide)) (widen s26004_1 (by decide))))))))))

theorem claim713 : CheckedClaim verifiedRow ⟨2,1,1,24016,27992,-945317534,1947330706⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 24016 3977 ⟨-945280912,1947294084⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide)))))))))))

theorem claim714 : CheckedClaim verifiedRow ⟨2,1,1,25908,27896,-826928084,1190550488⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 25908 1989 ⟨-826891462,1190513866⟩
  rw [← get_eq_raw]
  exact (append (widen s25908_4 (by decide)) (append (widen s25912_8 (by decide)) (append (widen s25920_64 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide)))))))))))))

theorem claim715 : CheckedClaim verifiedRow ⟨2,1,1,25940,27928,-866286178,1167213142⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 25940 1989 ⟨-866249556,1167176520⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide)))))))))))

theorem claim716 : CheckedClaim verifiedRow ⟨2,1,1,25972,27960,-905751450,1143525393⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 25972 1989 ⟨-905714828,1143488771⟩
  rw [← get_eq_raw]
  exact (append (widen s25972_4 (by decide)) (append (widen s25976_8 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim717 : CheckedClaim verifiedRow ⟨2,1,1,26004,27992,-945317534,1119488498⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 26004 1989 ⟨-945280912,1119451876⟩
  rw [← get_eq_raw]
  exact (append (widen s26004_4 (by decide)) (append (widen s26008_8 (by decide)) (append (widen s26016_32 (by decide)) (append (widen s26048_64 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide))))))))))))

private theorem s28160_512 : Run get 28160 512 ⟨-1796405515,-1154399905⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨-2426038389,-1797658238⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨-3011931621,-2427235179⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨-3011931621,-1797658238⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

theorem claim718 : CheckedClaim verifiedRow ⟨2,1,1,27960,29948,-3276193608,-905678200⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 27960 1989 ⟨-3276156986,-905714822⟩
  rw [← get_eq_raw]
  exact (append (widen s27960_8 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_64 (by decide)) (append (widen s29888_32 (by decide)) (append (widen s29920_16 (by decide)) (append (widen s29936_8 (by decide)) (append (widen s29944_4 (by decide)) (widen s29948_1 (by decide)))))))))))))

private theorem s29696_512 : Run get 29696 512 ⟨-3524557709,-3013013561⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨-3937044266,-3525469058⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨-3937044266,-3013013561⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨-3937044266,-1797658238⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨-4227135839,-3937736455⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨-4378868107,-4227571073⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨-4378868107,-3937736455⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim719 : CheckedClaim verifiedRow ⟨2,1,1,27960,31936,-4398197544,-905678200⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 27960 3977 ⟨-4398160922,-905714822⟩
  rw [← get_eq_raw]
  exact (append (widen s27960_8 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide))))))))))

theorem claim720 : CheckedClaim verifiedRow ⟨2,1,1,27992,29980,-3308163674,-945244284⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 27992 1989 ⟨-3308127052,-945280906⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_256 (by decide)) (append (widen s29952_16 (by decide)) (append (widen s29968_8 (by decide)) (append (widen s29976_4 (by decide)) (widen s29980_1 (by decide)))))))))))

theorem claim721 : CheckedClaim verifiedRow ⟨2,1,1,27992,31968,-4399358952,-945244284⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 27992 3977 ⟨-4399322330,-945280906⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim722 : CheckedClaim verifiedRow ⟨2,1,1,29916,31904,-4396455750,-3243809240⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 29916 1989 ⟨-4396419128,-3243845862⟩
  rw [← get_eq_raw]
  exact (append (widen s29916_4 (by decide)) (append (widen s29920_32 (by decide)) (append (widen s29952_256 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide)))))))))

theorem claim723 : CheckedClaim verifiedRow ⟨2,1,1,29948,31936,-4398197544,-3276120358⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 29948 1989 ⟨-4398160922,-3276156980⟩
  rw [← get_eq_raw]
  exact (append (widen s29948_4 (by decide)) (append (widen s29952_256 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide))))))))

theorem claim724 : CheckedClaim verifiedRow ⟨2,1,1,29980,31968,-4399358952,-3308090424⟩ := by
  change Run (rawBlock verifiedRow 2 1 .first) 29980 1989 ⟨-4399322330,-3308127046⟩
  rw [← get_eq_raw]
  exact (append (widen s29980_4 (by decide)) (append (widen s29984_32 (by decide)) (append (widen s30016_64 (by decide)) (append (widen s30080_128 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
