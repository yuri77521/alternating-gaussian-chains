import Point22AtlasRangeGroup112Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf112

private abbrev get := fastBlock verifiedRow 1 1 .second
private theorem get_eq_raw : get = rawBlock verifiedRow 1 1 .second :=
  funext (fastBlock_eq_raw verifiedRow 1 1 .second)

private theorem s512_512 : Run get 512 512 ⟨-4326005468812,-4108713621254⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

private theorem s1024_512 : Run get 1024 512 ⟨-4108154540036,-3759322203874⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

theorem claim368 : CheckedClaim verifiedRow ⟨1,1,2,32,2020,-4399709768237,-3323996476655⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 32 1989 ⟨-4399709499682,-3323996745210⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_512 (by decide)) (append (widen s1536_256 (by decide)) (append (widen s1792_128 (by decide)) (append (widen s1920_64 (by decide)) (append (widen s1984_32 (by decide)) (append (widen s2016_4 (by decide)) (widen s2020_1 (by decide)))))))))))))

private theorem s1536_512 : Run get 1536 512 ⟨-3758522262720,-3297190610873⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨-4108154540036,-3297190610873⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

private theorem s2048_512 : Run get 2048 512 ⟨-3296193044510,-2746950566814⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

theorem claim369 : CheckedClaim verifiedRow ⟨1,1,2,32,3014,-4399709768237,-2206895865045⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 32 2983 ⟨-4399709499682,-2206896133600⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_512 (by decide)) (append (widen s2560_256 (by decide)) (append (widen s2816_128 (by decide)) (append (widen s2944_64 (by decide)) (append (widen s3008_4 (by decide)) (append (widen s3012_2 (by decide)) (widen s3014_1 (by decide))))))))))))))

private theorem s2560_512 : Run get 2560 512 ⟨-2745807774604,-2136963748034⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨-3296193044510,-2136963748034⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨-2135733460607,-1497288039446⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

theorem claim370 : CheckedClaim verifiedRow ⟨1,1,2,32,4008,-4399709768237,-965095684512⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 32 3977 ⟨-4399709499682,-965095953067⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_32 (by decide)) (append (widen s4000_8 (by decide)) (widen s4008_1 (by decide))))))))))))))

private theorem s3584_512 : Run get 3584 512 ⟨-1496029268644,-857626068877⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨-2135733460607,-857626068877⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

private theorem s2048_2048 : Run get 2048 2048 ⟨-3296193044510,-857626068877⟩ :=
  join s2048_1024 s3072_1024 (by decide) (by decide)

private theorem s4096_512 : Run get 4096 512 ⟨-856395203045,-245433828713⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

private theorem s4608_512 : Run get 4608 512 ⟨-244281199679,315659816340⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨-856395203045,315659816340⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨316692636688,807013159570⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

theorem claim371 : CheckedClaim verifiedRow ⟨1,1,2,32,5996,-4399709768237,1107317640889⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 32 5965 ⟨-4399709499682,1107317372334⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide))))))))))))))))

private theorem s5632_512 : Run get 5632 512 ⟨807895165896,1215651197148⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨316692636688,1215651197148⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨-856395203045,1215651197148⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨1216362794008,1534456079078⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨1534988992580,1761907019315⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨1216362794008,1761907019315⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨1762263393214,1901446160136⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim372 : CheckedClaim verifiedRow ⟨1,1,2,32,7984,-4399709768237,1945733758896⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 32 7953 ⟨-4399709499682,1945733490341⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))))))))))

private theorem s7680_512 : Run get 7680 512 ⟨1901637015058,1960572341418⟩ :=
  join s7680_256 s7936_256 (by decide) (by decide)

private theorem s7168_1024 : Run get 7168 1024 ⟨1762263393214,1960572341418⟩ :=
  join s7168_512 s7680_512 (by decide) (by decide)

private theorem s6144_2048 : Run get 6144 2048 ⟨1216362794008,1960572341418⟩ :=
  join s6144_1024 s7168_1024 (by decide) (by decide)

private theorem s4096_4096 : Run get 4096 4096 ⟨-856395203045,1960572341418⟩ :=
  join s4096_2048 s6144_2048 (by decide) (by decide)

private theorem s8192_512 : Run get 8192 512 ⟨1949776370839,1964161705846⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

private theorem s8704_512 : Run get 8704 512 ⟨1881429776914,1949694746720⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨1881429776914,1964161705846⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨1768726250296,1881248552970⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

private theorem s9728_512 : Run get 9728 512 ⟨1624754179396,1768471366904⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨1624754179396,1881248552970⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨1624754179396,1964161705846⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨1461753467065,1624450578018⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨1290583692260,1461423840837⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨1290583692260,1624450578018⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨1120406635476,1290247659567⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

theorem claim373 : CheckedClaim verifiedRow ⟨1,1,2,32,11960,-4399709768237,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 32 11929 ⟨-4399709499682,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide)))))))))))))))))

theorem claim374 : CheckedClaim verifiedRow ⟨1,1,2,64,2052,-4398838647822,-3292199141497⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 64 1989 ⟨-4398838379267,-3292199410052⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide))))))))

theorem claim375 : CheckedClaim verifiedRow ⟨1,1,2,64,4040,-4398838647822,-925481328884⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 64 3977 ⟨-4398838379267,-925481597439⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))

theorem claim376 : CheckedClaim verifiedRow ⟨1,1,2,64,6028,-4398838647822,1131528672293⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 64 5965 ⟨-4398838379267,1131528403738⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide))))))))))))))

theorem claim377 : CheckedClaim verifiedRow ⟨1,1,2,64,8016,-4398838647822,1948806565392⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 64 7953 ⟨-4398838379267,1948806296837⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide))))))))))))))

theorem claim378 : CheckedClaim verifiedRow ⟨1,1,2,96,2084,-4397386993392,-3260057444652⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 96 1989 ⟨-4397386724837,-3260057713207⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_32 (by decide)) (append (widen s2080_4 (by decide)) (widen s2084_1 (by decide)))))))))

theorem claim379 : CheckedClaim verifiedRow ⟨1,1,2,96,4072,-4397386993392,-885964585929⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 96 3977 ⟨-4397386724837,-885964854484⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide))))))))))))))

theorem claim380 : CheckedClaim verifiedRow ⟨1,1,2,96,6060,-4397386993392,1155391209848⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 96 5965 ⟨-4397386724837,1155390941293⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))))))

theorem claim381 : CheckedClaim verifiedRow ⟨1,1,2,96,8048,-4397386993392,1951590456250⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 96 7953 ⟨-4397386724837,1951590187695⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))))))

theorem claim382 : CheckedClaim verifiedRow ⟨1,1,2,96,12024,-4397386993392,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 96 11929 ⟨-4397386724837,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))))))

theorem claim383 : CheckedClaim verifiedRow ⟨1,1,2,160,4136,-4392743487380,-807249448066⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 160 3977 ⟨-4392743218825,-807249716621⟩
  rw [← get_eq_raw]
  exact (append (widen s160_32 (by decide)) (append (widen s192_64 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_32 (by decide)) (append (widen s4128_8 (by decide)) (widen s4136_1 (by decide))))))))))

theorem claim384 : CheckedClaim verifiedRow ⟨1,1,2,1026,3014,-4107035131397,-2206895865045⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 1026 1989 ⟨-4107034862842,-2206896133600⟩
  rw [← get_eq_raw]
  exact (append (widen s1026_2 (by decide)) (append (widen s1028_4 (by decide)) (append (widen s1032_8 (by decide)) (append (widen s1040_16 (by decide)) (append (widen s1056_32 (by decide)) (append (widen s1088_64 (by decide)) (append (widen s1152_128 (by decide)) (append (widen s1280_256 (by decide)) (append (widen s1536_512 (by decide)) (append (widen s2048_512 (by decide)) (append (widen s2560_256 (by decide)) (append (widen s2816_128 (by decide)) (append (widen s2944_64 (by decide)) (append (widen s3008_4 (by decide)) (append (widen s3012_2 (by decide)) (widen s3014_1 (by decide)))))))))))))))))

theorem claim385 : CheckedClaim verifiedRow ⟨1,1,2,1026,4008,-4107035131397,-965095684512⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 1026 2983 ⟨-4107034862842,-965095953067⟩
  rw [← get_eq_raw]
  exact (append (widen s1026_2 (by decide)) (append (widen s1028_4 (by decide)) (append (widen s1032_8 (by decide)) (append (widen s1040_16 (by decide)) (append (widen s1056_32 (by decide)) (append (widen s1088_64 (by decide)) (append (widen s1152_128 (by decide)) (append (widen s1280_256 (by decide)) (append (widen s1536_512 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_32 (by decide)) (append (widen s4000_8 (by decide)) (widen s4008_1 (by decide)))))))))))))))))

theorem claim386 : CheckedClaim verifiedRow ⟨1,1,2,2020,3014,-3323997013768,-2206895865045⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2020 995 ⟨-3323996745213,-2206896133600⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_512 (by decide)) (append (widen s2560_256 (by decide)) (append (widen s2816_128 (by decide)) (append (widen s2944_64 (by decide)) (append (widen s3008_4 (by decide)) (append (widen s3012_2 (by decide)) (widen s3014_1 (by decide)))))))))))

theorem claim387 : CheckedClaim verifiedRow ⟨1,1,2,2020,4008,-3323997013768,-965095684512⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2020 1989 ⟨-3323996745213,-965095953067⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_32 (by decide)) (append (widen s4000_8 (by decide)) (widen s4008_1 (by decide)))))))))))

theorem claim388 : CheckedClaim verifiedRow ⟨1,1,2,2020,5002,-3323997013768,193003365266⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2020 2983 ⟨-3323996745213,193003096711⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_8 (by decide)) (append (widen s5000_2 (by decide)) (widen s5002_1 (by decide)))))))))))

theorem claim389 : CheckedClaim verifiedRow ⟨1,1,2,2020,5996,-3323997013768,1107317640889⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2020 3977 ⟨-3323996745213,1107317372334⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide)))))))))))))

theorem claim390 : CheckedClaim verifiedRow ⟨1,1,2,2020,7984,-3323997013768,1945733758896⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2020 5965 ⟨-3323996745213,1945733490341⟩
  rw [← get_eq_raw]
  exact (append (widen s2020_4 (by decide)) (append (widen s2024_8 (by decide)) (append (widen s2032_16 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))))))

theorem claim391 : CheckedClaim verifiedRow ⟨1,1,2,2052,4040,-3292199678610,-925481328884⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2052 1989 ⟨-3292199410055,-925481597439⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))))

theorem claim392 : CheckedClaim verifiedRow ⟨1,1,2,2052,6028,-3292199678610,1131528672293⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2052 3977 ⟨-3292199410055,1131528403738⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide)))))))))))))))))

theorem claim393 : CheckedClaim verifiedRow ⟨1,1,2,2052,8016,-3292199678610,1948806565392⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2052 5965 ⟨-3292199410055,1948806296837⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))))))))

theorem claim394 : CheckedClaim verifiedRow ⟨1,1,2,2084,4072,-3260057981765,-885964585929⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2084 1989 ⟨-3260057713210,-885964854484⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide)))))))))))))))

theorem claim395 : CheckedClaim verifiedRow ⟨1,1,2,2084,6060,-3260057981765,1155391209848⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2084 3977 ⟨-3260057713210,1155390941293⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))))))))

theorem claim396 : CheckedClaim verifiedRow ⟨1,1,2,2084,8048,-3260057981765,1951590456250⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2084 5965 ⟨-3260057713210,1951590187695⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))))))))

theorem claim397 : CheckedClaim verifiedRow ⟨1,1,2,2116,8080,-3227578549738,1954088134584⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 2116 5965 ⟨-3227578281183,1954087866029⟩
  rw [← get_eq_raw]
  exact (append (widen s2116_4 (by decide)) (append (widen s2120_8 (by decide)) (append (widen s2128_16 (by decide)) (append (widen s2144_32 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide))))))))))))))))

theorem claim398 : CheckedClaim verifiedRow ⟨1,1,2,3014,5002,-2206896402158,193003365266⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 3014 1989 ⟨-2206896133603,193003096711⟩
  rw [← get_eq_raw]
  exact (append (widen s3014_2 (by decide)) (append (widen s3016_8 (by decide)) (append (widen s3024_16 (by decide)) (append (widen s3040_32 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_8 (by decide)) (append (widen s5000_2 (by decide)) (widen s5002_1 (by decide))))))))))))

theorem claim399 : CheckedClaim verifiedRow ⟨1,1,2,3014,5996,-2206896402158,1107317640889⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 3014 2983 ⟨-2206896133603,1107317372334⟩
  rw [← get_eq_raw]
  exact (append (widen s3014_2 (by decide)) (append (widen s3016_8 (by decide)) (append (widen s3024_16 (by decide)) (append (widen s3040_32 (by decide)) (append (widen s3072_1024 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide))))))))))))))

theorem claim400 : CheckedClaim verifiedRow ⟨1,1,2,4008,5002,-965096221625,193003365266⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4008 995 ⟨-965095953070,193003096711⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_8 (by decide)) (append (widen s5000_2 (by decide)) (widen s5002_1 (by decide))))))))))

theorem claim401 : CheckedClaim verifiedRow ⟨1,1,2,4008,5996,-965096221625,1107317640889⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4008 1989 ⟨-965095953070,1107317372334⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_64 (by decide)) (append (widen s5952_32 (by decide)) (append (widen s5984_8 (by decide)) (append (widen s5992_4 (by decide)) (widen s5996_1 (by decide))))))))))))

theorem claim402 : CheckedClaim verifiedRow ⟨1,1,2,4008,6990,-965096221625,1693488870401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4008 2983 ⟨-965095953070,1693488601846⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_64 (by decide)) (append (widen s6976_8 (by decide)) (append (widen s6984_4 (by decide)) (append (widen s6988_2 (by decide)) (widen s6990_1 (by decide))))))))))))

theorem claim403 : CheckedClaim verifiedRow ⟨1,1,2,4008,7984,-965096221625,1945733758896⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4008 3977 ⟨-965095953070,1945733490341⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))))))

theorem claim404 : CheckedClaim verifiedRow ⟨1,1,2,4008,9972,-965096221625,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4008 5965 ⟨-965095953070,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide)))))))))))))

theorem claim405 : CheckedClaim verifiedRow ⟨1,1,2,4008,11960,-965096221625,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4008 7953 ⟨-965095953070,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide)))))))))))))

private theorem s11776_512 : Run get 11776 512 ⟨958566374953,1120080321384⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨958566374953,1290247659567⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨958566374953,1624450578018⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨958566374953,1964161705846⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨810635791531,958262351768⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨680589694569,810363307334⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨680589694569,958262351768⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨571061453307,680355107176⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

private theorem s13824_512 : Run get 13824 512 ⟨483641028942,570868785206⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨483641028942,680355107176⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨483641028942,958262351768⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨419176442764,483492564208⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨378046765496,419073297286⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨378046765496,483492564208⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨360381633312,377989374821⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim406 : CheckedClaim verifiedRow ⟨1,1,2,4008,15936,-965096221625,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4008 11929 ⟨-965095953070,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4008_8 (by decide)) (append (widen s4016_16 (by decide)) (append (widen s4032_64 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide)))))))))))

theorem claim407 : CheckedClaim verifiedRow ⟨1,1,2,4040,6028,-925481865997,1131528672293⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4040 1989 ⟨-925481597442,1131528403738⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide)))))))))))

theorem claim408 : CheckedClaim verifiedRow ⟨1,1,2,4040,7022,-925481865997,1706649041210⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4040 2983 ⟨-925481597442,1706648772655⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_64 (by decide)) (append (widen s6976_32 (by decide)) (append (widen s7008_8 (by decide)) (append (widen s7016_4 (by decide)) (append (widen s7020_2 (by decide)) (widen s7022_1 (by decide)))))))))))))

theorem claim409 : CheckedClaim verifiedRow ⟨1,1,2,4040,8016,-925481865997,1948806565392⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4040 3977 ⟨-925481597442,1948806296837⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim410 : CheckedClaim verifiedRow ⟨1,1,2,4040,10004,-925481865997,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4040 5965 ⟨-925481597442,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide)))))))))))

theorem claim411 : CheckedClaim verifiedRow ⟨1,1,2,4040,11992,-925481865997,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4040 7953 ⟨-925481597442,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide)))))))))))))

theorem claim412 : CheckedClaim verifiedRow ⟨1,1,2,4040,15968,-925481865997,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4040 11929 ⟨-925481597442,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))))

theorem claim413 : CheckedClaim verifiedRow ⟨1,1,2,4072,6060,-885965123042,1155391209848⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4072 1989 ⟨-885964854487,1155390941293⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))

theorem claim414 : CheckedClaim verifiedRow ⟨1,1,2,4072,8048,-885965123042,1951590456250⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4072 3977 ⟨-885964854487,1951590187695⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim415 : CheckedClaim verifiedRow ⟨1,1,2,4072,10036,-885965123042,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4072 5965 ⟨-885964854487,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide)))))))))))

theorem claim416 : CheckedClaim verifiedRow ⟨1,1,2,4072,12024,-885965123042,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4072 7953 ⟨-885964854487,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim417 : CheckedClaim verifiedRow ⟨1,1,2,4072,16000,-885965123042,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4072 11929 ⟨-885964854487,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))))

theorem claim418 : CheckedClaim verifiedRow ⟨1,1,2,4104,6092,-846552384897,1178903958324⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4104 1989 ⟨-846552116342,1178903689769⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_64 (by decide)) (append (widen s6080_8 (by decide)) (append (widen s6088_4 (by decide)) (widen s6092_1 (by decide)))))))))))))))

theorem claim419 : CheckedClaim verifiedRow ⟨1,1,2,4104,8080,-846552384897,1954088134584⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4104 3977 ⟨-846552116342,1954087866029⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide)))))))))))))))

theorem claim420 : CheckedClaim verifiedRow ⟨1,1,2,4104,10068,-846552384897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4104 5965 ⟨-846552116342,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_64 (by decide)) (append (widen s10048_16 (by decide)) (append (widen s10064_4 (by decide)) (widen s10068_1 (by decide)))))))))))))))))

theorem claim421 : CheckedClaim verifiedRow ⟨1,1,2,4104,16032,-846552384897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4104 11929 ⟨-846552116342,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))))))))

theorem claim422 : CheckedClaim verifiedRow ⟨1,1,2,4136,8112,-807249985179,1956302336842⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 4136 3977 ⟨-807249716624,1956302068287⟩
  rw [← get_eq_raw]
  exact (append (widen s4136_8 (by decide)) (append (widen s4144_16 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_16 (by decide)) (widen s8112_1 (by decide)))))))))))))))

theorem claim423 : CheckedClaim verifiedRow ⟨1,1,2,5034,7022,226903104988,1706649041210⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 5034 1989 ⟨226903373543,1706648772655⟩
  rw [← get_eq_raw]
  exact (append (widen s5034_2 (by decide)) (append (widen s5036_4 (by decide)) (append (widen s5040_16 (by decide)) (append (widen s5056_64 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_512 (by decide)) (append (widen s6656_256 (by decide)) (append (widen s6912_64 (by decide)) (append (widen s6976_32 (by decide)) (append (widen s7008_8 (by decide)) (append (widen s7016_4 (by decide)) (append (widen s7020_2 (by decide)) (widen s7022_1 (by decide))))))))))))))

theorem claim424 : CheckedClaim verifiedRow ⟨1,1,2,5034,8016,226903104988,1948806565392⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 5034 2983 ⟨226903373543,1948806296837⟩
  rw [← get_eq_raw]
  exact (append (widen s5034_2 (by decide)) (append (widen s5036_4 (by decide)) (append (widen s5040_16 (by decide)) (append (widen s5056_64 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide))))))))))))

theorem claim425 : CheckedClaim verifiedRow ⟨1,1,2,5996,7984,1107317103776,1945733758896⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 5996 1989 ⟨1107317372331,1945733490341⟩
  rw [← get_eq_raw]
  exact (append (widen s5996_4 (by decide)) (append (widen s6000_16 (by decide)) (append (widen s6016_128 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide))))))))))

theorem claim426 : CheckedClaim verifiedRow ⟨1,1,2,5996,9972,1107317103776,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 5996 3977 ⟨1107317372331,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s5996_4 (by decide)) (append (widen s6000_16 (by decide)) (append (widen s6016_128 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide)))))))))))))

theorem claim427 : CheckedClaim verifiedRow ⟨1,1,2,5996,11960,1060638486160,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 5996 5965 ⟨1060638754715,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s5996_4 (by decide)) (append (widen s6000_16 (by decide)) (append (widen s6016_128 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide)))))))))))))

theorem claim428 : CheckedClaim verifiedRow ⟨1,1,2,6028,8016,1131528135180,1948806565392⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6028 1989 ⟨1131528403735,1948806296837⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim429 : CheckedClaim verifiedRow ⟨1,1,2,6028,9010,1131528135180,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6028 2983 ⟨1131528403735,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_512 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_32 (by decide)) (append (widen s8992_16 (by decide)) (append (widen s9008_2 (by decide)) (widen s9010_1 (by decide))))))))))))

theorem claim430 : CheckedClaim verifiedRow ⟨1,1,2,6028,10004,1131528135180,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6028 3977 ⟨1131528403735,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide))))))))))))

theorem claim431 : CheckedClaim verifiedRow ⟨1,1,2,6028,11992,1050434023828,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6028 5965 ⟨1050434292383,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))))

theorem claim432 : CheckedClaim verifiedRow ⟨1,1,2,6060,8048,1155390672735,1951590456250⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6060 1989 ⟨1155390941290,1951590187695⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim433 : CheckedClaim verifiedRow ⟨1,1,2,6060,9042,1155390672735,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6060 2983 ⟨1155390941290,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_512 (by decide)) (append (widen s8704_256 (by decide)) (append (widen s8960_64 (by decide)) (append (widen s9024_16 (by decide)) (append (widen s9040_2 (by decide)) (widen s9042_1 (by decide)))))))))))

theorem claim434 : CheckedClaim verifiedRow ⟨1,1,2,6060,10036,1155390672735,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6060 3977 ⟨1155390941290,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))))

theorem claim435 : CheckedClaim verifiedRow ⟨1,1,2,6060,12024,1040272727897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6060 5965 ⟨1040272996452,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))))

theorem claim436 : CheckedClaim verifiedRow ⟨1,1,2,6092,8080,1178903421211,1954088134584⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6092 1989 ⟨1178903689766,1954087866029⟩
  rw [← get_eq_raw]
  exact (append (widen s6092_4 (by decide)) (append (widen s6096_16 (by decide)) (append (widen s6112_32 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide))))))))))

theorem claim437 : CheckedClaim verifiedRow ⟨1,1,2,6092,12056,1030155972324,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 6092 5965 ⟨1030156240879,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s6092_4 (by decide)) (append (widen s6096_16 (by decide)) (append (widen s6112_32 (by decide)) (append (widen s6144_2048 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide))))))))))))

theorem claim438 : CheckedClaim verifiedRow ⟨1,1,2,7022,10004,1693909405193,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 7022 2983 ⟨1693909673748,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s7022_2 (by decide)) (append (widen s7024_16 (by decide)) (append (widen s7040_128 (by decide)) (append (widen s7168_1024 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide)))))))))))

theorem claim439 : CheckedClaim verifiedRow ⟨1,1,2,7054,10036,1684768754793,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 7054 2983 ⟨1684769023348,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s7054_2 (by decide)) (append (widen s7056_16 (by decide)) (append (widen s7072_32 (by decide)) (append (widen s7104_64 (by decide)) (append (widen s7168_1024 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide)))))))))))))

theorem claim440 : CheckedClaim verifiedRow ⟨1,1,2,7984,9972,1702954730349,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 7984 1989 ⟨1702954998904,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide))))))))))))

theorem claim441 : CheckedClaim verifiedRow ⟨1,1,2,7984,11960,1060638486160,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 7984 3977 ⟨1060638754715,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide))))))))))))

theorem claim442 : CheckedClaim verifiedRow ⟨1,1,2,7984,13948,547635754367,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 7984 5965 ⟨547636022922,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_64 (by decide)) (append (widen s13888_32 (by decide)) (append (widen s13920_16 (by decide)) (append (widen s13936_8 (by decide)) (append (widen s13944_4 (by decide)) (widen s13948_1 (by decide)))))))))))))

theorem claim443 : CheckedClaim verifiedRow ⟨1,1,2,7984,15936,359819175999,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 7984 7953 ⟨359819444554,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide))))))))))

private theorem s15872_512 : Run get 15872 512 ⟨359635886583,366209348103⟩ :=
  join s15872_256 s16128_256 (by decide) (by decide)

private theorem s15360_1024 : Run get 15360 1024 ⟨359635886583,377989374821⟩ :=
  join s15360_512 s15872_512 (by decide) (by decide)

private theorem s14336_2048 : Run get 14336 2048 ⟨359635886583,483492564208⟩ :=
  join s14336_1024 s15360_1024 (by decide) (by decide)

private theorem s12288_4096 : Run get 12288 4096 ⟨359635886583,958262351768⟩ :=
  join s12288_2048 s14336_2048 (by decide) (by decide)

private theorem s8192_8192 : Run get 8192 8192 ⟨359635886583,1964161705846⟩ :=
  join s8192_4096 s12288_4096 (by decide) (by decide)

private theorem s16384_512 : Run get 16384 512 ⟨366243717602,395522408299⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨395602614792,448255762656⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨366243717602,448255762656⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨448381566009,524179334109⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

private theorem s17920_512 : Run get 17920 512 ⟨524350013956,622712681807⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨448381566009,622712681807⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨366243717602,622712681807⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨622926607711,742676278294⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨742930374778,882000826443⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨622926607711,882000826443⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

theorem claim444 : CheckedClaim verifiedRow ⟨1,1,2,7984,19912,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 7984 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide))))))))))))

theorem claim445 : CheckedClaim verifiedRow ⟨1,1,2,8016,10004,1693909405193,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8016 1989 ⟨1693909673748,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide))))))))))

theorem claim446 : CheckedClaim verifiedRow ⟨1,1,2,8016,10998,1379589793149,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8016 2983 ⟨1379590061704,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_128 (by decide)) (append (widen s10880_64 (by decide)) (append (widen s10944_32 (by decide)) (append (widen s10976_16 (by decide)) (append (widen s10992_4 (by decide)) (append (widen s10996_2 (by decide)) (widen s10998_1 (by decide)))))))))))))

theorem claim447 : CheckedClaim verifiedRow ⟨1,1,2,8016,11992,1050434023828,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8016 3977 ⟨1050434292383,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))

theorem claim448 : CheckedClaim verifiedRow ⟨1,1,2,8016,13980,541853166906,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8016 5965 ⟨541853435461,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide))))))))))))

theorem claim449 : CheckedClaim verifiedRow ⟨1,1,2,8016,15968,359681507556,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8016 7953 ⟨359681776111,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))

theorem claim450 : CheckedClaim verifiedRow ⟨1,1,2,8016,19944,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8016 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide)))))))))))))

theorem claim451 : CheckedClaim verifiedRow ⟨1,1,2,8048,10036,1684768754793,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8048 1989 ⟨1684769023348,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))

theorem claim452 : CheckedClaim verifiedRow ⟨1,1,2,8048,12024,1040272727897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8048 3977 ⟨1040272996452,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))

theorem claim453 : CheckedClaim verifiedRow ⟨1,1,2,8048,14012,536158419808,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8048 5965 ⟨536158688363,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide))))))))))))

theorem claim454 : CheckedClaim verifiedRow ⟨1,1,2,8048,16000,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8048 7953 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide)))))))))

private theorem s19456_512 : Run get 19456 512 ⟨882289981658,1037423098406⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

theorem claim455 : CheckedClaim verifiedRow ⟨1,1,2,8048,19976,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8048 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide)))))))))

theorem claim456 : CheckedClaim verifiedRow ⟨1,1,2,8080,10068,1675535762463,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8080 1989 ⟨1675536031018,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_64 (by decide)) (append (widen s10048_16 (by decide)) (append (widen s10064_4 (by decide)) (widen s10068_1 (by decide)))))))))))

theorem claim457 : CheckedClaim verifiedRow ⟨1,1,2,8080,12056,1030155972324,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8080 3977 ⟨1030156240879,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

theorem claim458 : CheckedClaim verifiedRow ⟨1,1,2,8080,14044,530551736065,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8080 5965 ⟨530552004620,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide)))))))))))))

theorem claim459 : CheckedClaim verifiedRow ⟨1,1,2,8080,16032,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8080 7953 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim460 : CheckedClaim verifiedRow ⟨1,1,2,8080,20008,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8080 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim461 : CheckedClaim verifiedRow ⟨1,1,2,8112,12088,1020085104853,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8112 3977 ⟨1020085373408,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_32 (by decide)) (append (widen s12064_16 (by decide)) (append (widen s12080_8 (by decide)) (widen s12088_1 (by decide)))))))))))

theorem claim462 : CheckedClaim verifiedRow ⟨1,1,2,8978,9972,1702954730349,1919388287385⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8978 995 ⟨1702954998904,1919388018830⟩
  rw [← get_eq_raw]
  exact (append (widen s8978_2 (by decide)) (append (widen s8980_4 (by decide)) (append (widen s8984_8 (by decide)) (append (widen s8992_32 (by decide)) (append (widen s9024_64 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_128 (by decide)) (append (widen s9856_64 (by decide)) (append (widen s9920_32 (by decide)) (append (widen s9952_16 (by decide)) (append (widen s9968_4 (by decide)) (widen s9972_1 (by decide))))))))))))))

theorem claim463 : CheckedClaim verifiedRow ⟨1,1,2,8978,11960,1060638486160,1919388287385⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 8978 2983 ⟨1060638754715,1919388018830⟩
  rw [← get_eq_raw]
  exact (append (widen s8978_2 (by decide)) (append (widen s8980_4 (by decide)) (append (widen s8984_8 (by decide)) (append (widen s8992_32 (by decide)) (append (widen s9024_64 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide)))))))))))))))

theorem claim464 : CheckedClaim verifiedRow ⟨1,1,2,9010,11992,1050434023828,1914866087362⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 9010 2983 ⟨1050434292383,1914865818807⟩
  rw [← get_eq_raw]
  exact (append (widen s9010_2 (by decide)) (append (widen s9012_4 (by decide)) (append (widen s9016_8 (by decide)) (append (widen s9024_64 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))))

theorem claim465 : CheckedClaim verifiedRow ⟨1,1,2,9042,12024,1040272727897,1910149771039⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 9042 2983 ⟨1040272996452,1910149502484⟩
  rw [← get_eq_raw]
  exact (append (widen s9042_2 (by decide)) (append (widen s9044_4 (by decide)) (append (widen s9048_8 (by decide)) (append (widen s9056_32 (by decide)) (append (widen s9088_128 (by decide)) (append (widen s9216_1024 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))))

theorem claim466 : CheckedClaim verifiedRow ⟨1,1,2,9972,11960,1060638486160,1702955267462⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 9972 1989 ⟨1060638754715,1702954998907⟩
  rw [← get_eq_raw]
  exact (append (widen s9972_4 (by decide)) (append (widen s9976_8 (by decide)) (append (widen s9984_256 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_32 (by decide)) (append (widen s11936_16 (by decide)) (append (widen s11952_8 (by decide)) (widen s11960_1 (by decide)))))))))))

theorem claim467 : CheckedClaim verifiedRow ⟨1,1,2,9972,13948,547635754367,1702955267462⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 9972 3977 ⟨547636022922,1702954998907⟩
  rw [← get_eq_raw]
  exact (append (widen s9972_4 (by decide)) (append (widen s9976_8 (by decide)) (append (widen s9984_256 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_64 (by decide)) (append (widen s13888_32 (by decide)) (append (widen s13920_16 (by decide)) (append (widen s13936_8 (by decide)) (append (widen s13944_4 (by decide)) (widen s13948_1 (by decide)))))))))))))

theorem claim468 : CheckedClaim verifiedRow ⟨1,1,2,9972,15936,359819175999,1702955267462⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 9972 5965 ⟨359819444554,1702954998907⟩
  rw [← get_eq_raw]
  exact (append (widen s9972_4 (by decide)) (append (widen s9976_8 (by decide)) (append (widen s9984_256 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide))))))))))

theorem claim469 : CheckedClaim verifiedRow ⟨1,1,2,10004,10998,1379589793149,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10004 995 ⟨1379590061704,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_512 (by decide)) (append (widen s10752_128 (by decide)) (append (widen s10880_64 (by decide)) (append (widen s10944_32 (by decide)) (append (widen s10976_16 (by decide)) (append (widen s10992_4 (by decide)) (append (widen s10996_2 (by decide)) (widen s10998_1 (by decide))))))))))))))

theorem claim470 : CheckedClaim verifiedRow ⟨1,1,2,10004,11992,1050434023828,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10004 1989 ⟨1050434292383,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide)))))))))))))

theorem claim471 : CheckedClaim verifiedRow ⟨1,1,2,10004,12986,760900168478,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10004 2983 ⟨760900437033,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_32 (by decide)) (append (widen s12960_16 (by decide)) (append (widen s12976_8 (by decide)) (append (widen s12984_2 (by decide)) (widen s12986_1 (by decide))))))))))))))

theorem claim472 : CheckedClaim verifiedRow ⟨1,1,2,10004,13980,541853166906,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10004 3977 ⟨541853435461,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide))))))))))))))

theorem claim473 : CheckedClaim verifiedRow ⟨1,1,2,10004,15968,359681507556,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10004 5965 ⟨359681776111,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))))

theorem claim474 : CheckedClaim verifiedRow ⟨1,1,2,10036,12024,1040272727897,1684769291906⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10036 1989 ⟨1040272996452,1684769023351⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim475 : CheckedClaim verifiedRow ⟨1,1,2,10036,13018,752640589652,1684769291906⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10036 2983 ⟨752640858207,1684769023351⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_64 (by decide)) (append (widen s12992_16 (by decide)) (append (widen s13008_8 (by decide)) (append (widen s13016_2 (by decide)) (widen s13018_1 (by decide)))))))))))))

theorem claim476 : CheckedClaim verifiedRow ⟨1,1,2,10036,14012,536158419808,1684769291906⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10036 3977 ⟨536158688363,1684769023351⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide))))))))))))))

theorem claim477 : CheckedClaim verifiedRow ⟨1,1,2,10036,16000,359635618028,1684769291906⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10036 5965 ⟨359635886583,1684769023351⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide)))))))))))

theorem claim478 : CheckedClaim verifiedRow ⟨1,1,2,10068,12056,1030155972324,1675536299576⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10068 1989 ⟨1030156240879,1675536031021⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

theorem claim479 : CheckedClaim verifiedRow ⟨1,1,2,10068,13050,744456243032,1675536299576⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10068 2983 ⟨744456511587,1675536031021⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_64 (by decide)) (append (widen s12992_32 (by decide)) (append (widen s13024_16 (by decide)) (append (widen s13040_8 (by decide)) (append (widen s13048_2 (by decide)) (widen s13050_1 (by decide))))))))))))))

theorem claim480 : CheckedClaim verifiedRow ⟨1,1,2,10068,14044,530551736065,1675536299576⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10068 3977 ⟨530552004620,1675536031021⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide))))))))))))))

theorem claim481 : CheckedClaim verifiedRow ⟨1,1,2,10068,16032,359635618028,1675536299576⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10068 5965 ⟨359635886583,1675536031021⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_2048 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))))))

theorem claim482 : CheckedClaim verifiedRow ⟨1,1,2,10966,13948,547635754367,1390301746240⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10966 2983 ⟨547636022922,1390301477685⟩
  rw [← get_eq_raw]
  exact (append (widen s10966_2 (by decide)) (append (widen s10968_8 (by decide)) (append (widen s10976_32 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_64 (by decide)) (append (widen s13888_32 (by decide)) (append (widen s13920_16 (by decide)) (append (widen s13936_8 (by decide)) (append (widen s13944_4 (by decide)) (widen s13948_1 (by decide))))))))))))))

theorem claim483 : CheckedClaim verifiedRow ⟨1,1,2,10998,12986,760900168478,1379590330262⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10998 1989 ⟨760900437033,1379590061707⟩
  rw [← get_eq_raw]
  exact (append (widen s10998_2 (by decide)) (append (widen s11000_8 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_32 (by decide)) (append (widen s12960_16 (by decide)) (append (widen s12976_8 (by decide)) (append (widen s12984_2 (by decide)) (widen s12986_1 (by decide))))))))))))

theorem claim484 : CheckedClaim verifiedRow ⟨1,1,2,10998,13980,541853166906,1379590330262⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 10998 2983 ⟨541853435461,1379590061707⟩
  rw [← get_eq_raw]
  exact (append (widen s10998_2 (by decide)) (append (widen s11000_8 (by decide)) (append (widen s11008_256 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide))))))))))))

theorem claim485 : CheckedClaim verifiedRow ⟨1,1,2,11030,14012,536158419808,1368865727390⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11030 2983 ⟨536158688363,1368865458835⟩
  rw [← get_eq_raw]
  exact (append (widen s11030_2 (by decide)) (append (widen s11032_8 (by decide)) (append (widen s11040_32 (by decide)) (append (widen s11072_64 (by decide)) (append (widen s11136_128 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide)))))))))))))))

theorem claim486 : CheckedClaim verifiedRow ⟨1,1,2,11062,14044,530551736065,1358130171834⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11062 2983 ⟨530552004620,1358129903279⟩
  rw [← get_eq_raw]
  exact (append (widen s11062_2 (by decide)) (append (widen s11064_8 (by decide)) (append (widen s11072_64 (by decide)) (append (widen s11136_128 (by decide)) (append (widen s11264_1024 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide))))))))))))))

theorem claim487 : CheckedClaim verifiedRow ⟨1,1,2,11960,13948,547635754367,1060639023273⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11960 1989 ⟨547636022922,1060638754718⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_64 (by decide)) (append (widen s13888_32 (by decide)) (append (widen s13920_16 (by decide)) (append (widen s13936_8 (by decide)) (append (widen s13944_4 (by decide)) (widen s13948_1 (by decide))))))))))))

theorem claim488 : CheckedClaim verifiedRow ⟨1,1,2,11960,14942,409775358163,1060639023273⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11960 2983 ⟨409775626718,1060638754718⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_512 (by decide)) (append (widen s14848_64 (by decide)) (append (widen s14912_16 (by decide)) (append (widen s14928_8 (by decide)) (append (widen s14936_4 (by decide)) (append (widen s14940_2 (by decide)) (widen s14942_1 (by decide))))))))))))

theorem claim489 : CheckedClaim verifiedRow ⟨1,1,2,11960,15936,359819175999,1060639023273⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11960 3977 ⟨359819444554,1060638754718⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide)))))))))

theorem claim490 : CheckedClaim verifiedRow ⟨1,1,2,11960,17924,359635618028,1060639023273⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11960 5965 ⟨359635886583,1060638754718⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_4 (by decide)) (widen s17924_1 (by decide)))))))))

theorem claim491 : CheckedClaim verifiedRow ⟨1,1,2,11960,19912,359635618028,1060639023273⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11960 7953 ⟨359635886583,1060638754718⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide))))))))))))

private theorem s19968_512 : Run get 19968 512 ⟨1037739578808,1204203380279⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨882289981658,1204203380279⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨622926607711,1204203380279⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨366243717602,1204203380279⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨1204536325589,1375904853403⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨1376239934317,1544277987920⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨1204536325589,1544277987920⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

private theorem s21504_512 : Run get 21504 512 ⟨1544597311150,1699292024221⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨1699574363037,1829349755781⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨1544597311150,1829349755781⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨1204536325589,1829349755781⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨1829571167460,1921710366105⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨1921845229642,1963127911628⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨1829571167460,1963127911628⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

theorem claim492 : CheckedClaim verifiedRow ⟨1,1,2,11960,23888,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11960 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s11960_8 (by decide)) (append (widen s11968_64 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_16 (by decide)) (widen s23888_1 (by decide))))))))))))

theorem claim493 : CheckedClaim verifiedRow ⟨1,1,2,11992,12986,760900168478,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11992 995 ⟨760900437033,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_512 (by decide)) (append (widen s12800_128 (by decide)) (append (widen s12928_32 (by decide)) (append (widen s12960_16 (by decide)) (append (widen s12976_8 (by decide)) (append (widen s12984_2 (by decide)) (widen s12986_1 (by decide)))))))))))

theorem claim494 : CheckedClaim verifiedRow ⟨1,1,2,11992,13980,541853166906,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11992 1989 ⟨541853435461,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide)))))))))))

theorem claim495 : CheckedClaim verifiedRow ⟨1,1,2,11992,14974,406790013861,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11992 2983 ⟨406790282416,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_512 (by decide)) (append (widen s14848_64 (by decide)) (append (widen s14912_32 (by decide)) (append (widen s14944_16 (by decide)) (append (widen s14960_8 (by decide)) (append (widen s14968_4 (by decide)) (append (widen s14972_2 (by decide)) (widen s14974_1 (by decide)))))))))))))

theorem claim496 : CheckedClaim verifiedRow ⟨1,1,2,11992,15968,359681507556,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11992 3977 ⟨359681776111,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim497 : CheckedClaim verifiedRow ⟨1,1,2,11992,17956,359635618028,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11992 5965 ⟨359635886583,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide))))))))))

theorem claim498 : CheckedClaim verifiedRow ⟨1,1,2,11992,19944,359635618028,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11992 7953 ⟨359635886583,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide)))))))))))))

theorem claim499 : CheckedClaim verifiedRow ⟨1,1,2,11992,23920,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 11992 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))))

theorem claim500 : CheckedClaim verifiedRow ⟨1,1,2,12024,14012,536158419808,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12024 1989 ⟨536158688363,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide)))))))))))

theorem claim501 : CheckedClaim verifiedRow ⟨1,1,2,12024,15006,403896073769,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12024 2983 ⟨403896342324,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_512 (by decide)) (append (widen s14848_128 (by decide)) (append (widen s14976_16 (by decide)) (append (widen s14992_8 (by decide)) (append (widen s15000_4 (by decide)) (append (widen s15004_2 (by decide)) (widen s15006_1 (by decide)))))))))))

theorem claim502 : CheckedClaim verifiedRow ⟨1,1,2,12024,16000,359635618028,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12024 3977 ⟨359635886583,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim503 : CheckedClaim verifiedRow ⟨1,1,2,12024,17988,359635618028,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12024 5965 ⟨359635886583,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide)))))))))

theorem claim504 : CheckedClaim verifiedRow ⟨1,1,2,12024,19976,359635618028,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12024 7953 ⟨359635886583,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide)))))))))

theorem claim505 : CheckedClaim verifiedRow ⟨1,1,2,12024,23952,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12024 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide)))))))))))

theorem claim506 : CheckedClaim verifiedRow ⟨1,1,2,12056,14044,530551736065,1030156509437⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12056 1989 ⟨530552004620,1030156240882⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide)))))))))))))

theorem claim507 : CheckedClaim verifiedRow ⟨1,1,2,12056,16032,359635618028,1030156509437⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12056 3977 ⟨359635886583,1030156240882⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim508 : CheckedClaim verifiedRow ⟨1,1,2,12056,18020,359635618028,1030156509437⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12056 5965 ⟨359635886583,1030156240882⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))))

theorem claim509 : CheckedClaim verifiedRow ⟨1,1,2,12056,20008,359635618028,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12056 7953 ⟨359635886583,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))))

theorem claim510 : CheckedClaim verifiedRow ⟨1,1,2,12056,23984,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12056 11929 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_4096 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))))

theorem claim511 : CheckedClaim verifiedRow ⟨1,1,2,12088,16064,359635618028,1020085641966⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12088 3977 ⟨359635886583,1020085373411⟩
  rw [← get_eq_raw]
  exact (append (widen s12088_8 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim512 : CheckedClaim verifiedRow ⟨1,1,2,12954,15936,359819175999,769234852257⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12954 2983 ⟨359819444554,769234583702⟩
  rw [← get_eq_raw]
  exact (append (widen s12954_2 (by decide)) (append (widen s12956_4 (by decide)) (append (widen s12960_32 (by decide)) (append (widen s12992_64 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_1024 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide)))))))))))

theorem claim513 : CheckedClaim verifiedRow ⟨1,1,2,12986,13980,541853166906,760900705591⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 12986 995 ⟨541853435461,760900437036⟩
  rw [← get_eq_raw]
  exact (append (widen s12986_2 (by decide)) (append (widen s12988_4 (by decide)) (append (widen s12992_64 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide)))))))))))

theorem claim514 : CheckedClaim verifiedRow ⟨1,1,2,13018,16000,359635618028,752641126765⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 13018 2983 ⟨359635886583,752640858210⟩
  rw [← get_eq_raw]
  exact (append (widen s13018_2 (by decide)) (append (widen s13020_4 (by decide)) (append (widen s13024_32 (by decide)) (append (widen s13056_256 (by decide)) (append (widen s13312_1024 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))))

theorem claim515 : CheckedClaim verifiedRow ⟨1,1,2,13948,17924,359635618028,547636291480⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 13948 3977 ⟨359635886583,547636022925⟩
  rw [← get_eq_raw]
  exact (append (widen s13948_4 (by decide)) (append (widen s13952_128 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_4 (by decide)) (widen s17924_1 (by decide)))))))))

theorem claim516 : CheckedClaim verifiedRow ⟨1,1,2,13948,19912,359635618028,1020085641966⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 13948 5965 ⟨359635886583,1020085373411⟩
  rw [← get_eq_raw]
  exact (append (widen s13948_4 (by decide)) (append (widen s13952_128 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide))))))))))))

theorem claim517 : CheckedClaim verifiedRow ⟨1,1,2,13980,15968,359681507556,541853704019⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 13980 1989 ⟨359681776111,541853435464⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim518 : CheckedClaim verifiedRow ⟨1,1,2,13980,17956,359635618028,541853704019⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 13980 3977 ⟨359635886583,541853435464⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide)))))))))))

theorem claim519 : CheckedClaim verifiedRow ⟨1,1,2,13980,19944,359635618028,1030156509437⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 13980 5965 ⟨359635886583,1030156240882⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))

theorem claim520 : CheckedClaim verifiedRow ⟨1,1,2,14012,15006,403896073769,536158956921⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14012 995 ⟨403896342324,536158688366⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_512 (by decide)) (append (widen s14848_128 (by decide)) (append (widen s14976_16 (by decide)) (append (widen s14992_8 (by decide)) (append (widen s15000_4 (by decide)) (append (widen s15004_2 (by decide)) (widen s15006_1 (by decide)))))))))))

theorem claim521 : CheckedClaim verifiedRow ⟨1,1,2,14012,16000,359635618028,536158956921⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14012 1989 ⟨359635886583,536158688366⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim522 : CheckedClaim verifiedRow ⟨1,1,2,14012,16994,359635618028,536158956921⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14012 2983 ⟨359635886583,536158688366⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_512 (by decide)) (append (widen s16896_64 (by decide)) (append (widen s16960_32 (by decide)) (append (widen s16992_2 (by decide)) (widen s16994_1 (by decide))))))))))

theorem claim523 : CheckedClaim verifiedRow ⟨1,1,2,14012,17988,359635618028,536158956921⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14012 3977 ⟨359635886583,536158688366⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide))))))))))

theorem claim524 : CheckedClaim verifiedRow ⟨1,1,2,14012,19976,359635618028,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14012 5965 ⟨359635886583,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))))

theorem claim525 : CheckedClaim verifiedRow ⟨1,1,2,14044,16032,359635618028,530552273178⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14044 1989 ⟨359635886583,530552004623⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))

theorem claim526 : CheckedClaim verifiedRow ⟨1,1,2,14044,18020,359635618028,541853704019⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14044 3977 ⟨359635886583,541853435464⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide)))))))))))

theorem claim527 : CheckedClaim verifiedRow ⟨1,1,2,14044,20008,359635618028,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 14044 5965 ⟨359635886583,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_2048 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim528 : CheckedClaim verifiedRow ⟨1,1,2,15006,16000,359635618028,403896610882⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15006 995 ⟨359635886583,403896342327⟩
  rw [← get_eq_raw]
  exact (append (widen s15006_2 (by decide)) (append (widen s15008_32 (by decide)) (append (widen s15040_64 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim529 : CheckedClaim verifiedRow ⟨1,1,2,15006,17988,359635618028,536158956921⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15006 2983 ⟨359635886583,536158688366⟩
  rw [← get_eq_raw]
  exact (append (widen s15006_2 (by decide)) (append (widen s15008_32 (by decide)) (append (widen s15040_64 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_1024 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide)))))))))))

theorem claim530 : CheckedClaim verifiedRow ⟨1,1,2,15038,18020,359635618028,541853704019⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15038 2983 ⟨359635886583,541853435464⟩
  rw [← get_eq_raw]
  exact (append (widen s15038_2 (by decide)) (append (widen s15040_64 (by decide)) (append (widen s15104_256 (by decide)) (append (widen s15360_1024 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide)))))))))))

theorem claim531 : CheckedClaim verifiedRow ⟨1,1,2,15936,19912,359635618028,1020085641966⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15936 3977 ⟨359635886583,1020085373411⟩
  rw [← get_eq_raw]
  exact (append (widen s15936_64 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide)))))))))))

theorem claim532 : CheckedClaim verifiedRow ⟨1,1,2,15936,21900,359635618028,1666213929835⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15936 5965 ⟨359635886583,1666213661280⟩
  rw [← get_eq_raw]
  exact (append (widen s15936_64 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_8 (by decide)) (append (widen s21896_4 (by decide)) (widen s21900_1 (by decide)))))))))))

theorem claim533 : CheckedClaim verifiedRow ⟨1,1,2,15936,23888,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15936 7953 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s15936_64 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_16 (by decide)) (widen s23888_1 (by decide)))))))))))

theorem claim534 : CheckedClaim verifiedRow ⟨1,1,2,15968,17956,359635618028,530552273178⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15968 1989 ⟨359635886583,530552004623⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide)))))))))

theorem claim535 : CheckedClaim verifiedRow ⟨1,1,2,15968,19944,359635618028,1030156509437⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15968 3977 ⟨359635886583,1030156240882⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))

theorem claim536 : CheckedClaim verifiedRow ⟨1,1,2,15968,21932,359635618028,1675536299576⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15968 5965 ⟨359635886583,1675536031021⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_32 (by decide)) (append (widen s21920_8 (by decide)) (append (widen s21928_4 (by decide)) (widen s21932_1 (by decide))))))))))))

theorem claim537 : CheckedClaim verifiedRow ⟨1,1,2,15968,23920,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15968 7953 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide))))))))))))

private theorem s23552_512 : Run get 23552 512 ⟨1940690919504,1964161705846⟩ :=
  join s23552_256 s23808_256 (by decide) (by decide)

private theorem s24064_512 : Run get 24064 512 ⟨1842823167667,1940576735662⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s23552_1024 : Run get 23552 1024 ⟨1842823167667,1964161705846⟩ :=
  join s23552_512 s24064_512 (by decide) (by decide)

private theorem s22528_2048 : Run get 22528 2048 ⟨1829571167460,1964161705846⟩ :=
  join s22528_1024 s23552_1024 (by decide) (by decide)

private theorem s20480_4096 : Run get 20480 4096 ⟨1204536325589,1964161705846⟩ :=
  join s20480_2048 s22528_2048 (by decide) (by decide)

private theorem s16384_8192 : Run get 16384 8192 ⟨366243717602,1964161705846⟩ :=
  join s16384_4096 s20480_4096 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨1660379625054,1842551736188⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨1387748046496,1659936191801⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨1387748046496,1842551736188⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

private theorem s25600_512 : Run get 25600 512 ⟨1023849462191,1387125787671⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨572923222275,1023051264925⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨572923222275,1387125787671⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨572923222275,1842551736188⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨44987044814,571962933466⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨-544118944907,43889987857⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨-544118944907,571962933466⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

theorem claim538 : CheckedClaim verifiedRow ⟨1,1,2,15968,27896,-846552384897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 15968 11929 ⟨-846552116342,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide)))))))))))))

theorem claim539 : CheckedClaim verifiedRow ⟨1,1,2,16000,16994,359635618028,403896610882⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16000 995 ⟨359635886583,403896342327⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_512 (by decide)) (append (widen s16896_64 (by decide)) (append (widen s16960_32 (by decide)) (append (widen s16992_2 (by decide)) (widen s16994_1 (by decide))))))))

theorem claim540 : CheckedClaim verifiedRow ⟨1,1,2,16000,17988,359635618028,536158956921⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16000 1989 ⟨359635886583,536158688366⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide))))))))

theorem claim541 : CheckedClaim verifiedRow ⟨1,1,2,16000,19976,359635618028,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16000 3977 ⟨359635886583,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))

theorem claim542 : CheckedClaim verifiedRow ⟨1,1,2,16000,21964,359635618028,1684769291906⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16000 5965 ⟨359635886583,1684769023351⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide)))))))))))

theorem claim543 : CheckedClaim verifiedRow ⟨1,1,2,16000,23952,359635618028,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16000 7953 ⟨359635886583,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide))))))))))

theorem claim544 : CheckedClaim verifiedRow ⟨1,1,2,16000,27928,-885965123042,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16000 11929 ⟨-885964854487,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide))))))))))

theorem claim545 : CheckedClaim verifiedRow ⟨1,1,2,16032,18020,359681507556,541853704019⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16032 1989 ⟨359681776111,541853435464⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))

theorem claim546 : CheckedClaim verifiedRow ⟨1,1,2,16032,20008,359681507556,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16032 3977 ⟨359681776111,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))

theorem claim547 : CheckedClaim verifiedRow ⟨1,1,2,16032,21996,359681507556,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16032 5965 ⟨359681776111,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide)))))))))))))

theorem claim548 : CheckedClaim verifiedRow ⟨1,1,2,16032,23984,359681507556,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16032 7953 ⟨359681776111,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))

theorem claim549 : CheckedClaim verifiedRow ⟨1,1,2,16064,20040,359819175999,1060639023273⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16064 3977 ⟨359819444554,1060638754718⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide)))))))))

theorem claim550 : CheckedClaim verifiedRow ⟨1,1,2,16930,19912,398382548394,1020085641966⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16930 2983 ⟨398382816949,1020085373411⟩
  rw [← get_eq_raw]
  exact (append (widen s16930_2 (by decide)) (append (widen s16932_4 (by decide)) (append (widen s16936_8 (by decide)) (append (widen s16944_16 (by decide)) (append (widen s16960_64 (by decide)) (append (widen s17024_128 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_1024 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_8 (by decide)) (widen s19912_1 (by decide)))))))))))))))

theorem claim551 : CheckedClaim verifiedRow ⟨1,1,2,16962,19944,401093574128,1030156509437⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16962 2983 ⟨401093842683,1030156240882⟩
  rw [← get_eq_raw]
  exact (append (widen s16962_2 (by decide)) (append (widen s16964_4 (by decide)) (append (widen s16968_8 (by decide)) (append (widen s16976_16 (by decide)) (append (widen s16992_32 (by decide)) (append (widen s17024_128 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_1024 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))))

theorem claim552 : CheckedClaim verifiedRow ⟨1,1,2,16994,17988,403896073769,536158956921⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 16994 995 ⟨403896342324,536158688366⟩
  rw [← get_eq_raw]
  exact (append (widen s16994_2 (by decide)) (append (widen s16996_4 (by decide)) (append (widen s17000_8 (by decide)) (append (widen s17008_16 (by decide)) (append (widen s17024_128 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide)))))))))))

theorem claim553 : CheckedClaim verifiedRow ⟨1,1,2,17026,20008,406790013861,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17026 2983 ⟨406790282416,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s17026_2 (by decide)) (append (widen s17028_4 (by decide)) (append (widen s17032_8 (by decide)) (append (widen s17040_16 (by decide)) (append (widen s17056_32 (by decide)) (append (widen s17088_64 (by decide)) (append (widen s17152_256 (by decide)) (append (widen s17408_1024 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))))))

theorem claim554 : CheckedClaim verifiedRow ⟨1,1,2,17924,21900,525033329057,1666213929835⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17924 3977 ⟨525033597612,1666213661280⟩
  rw [← get_eq_raw]
  exact (append (widen s17924_4 (by decide)) (append (widen s17928_8 (by decide)) (append (widen s17936_16 (by decide)) (append (widen s17952_32 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_8 (by decide)) (append (widen s21896_4 (by decide)) (widen s21900_1 (by decide)))))))))))))))

theorem claim555 : CheckedClaim verifiedRow ⟨1,1,2,17924,23888,525033329057,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17924 5965 ⟨525033597612,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s17924_4 (by decide)) (append (widen s17928_8 (by decide)) (append (widen s17936_16 (by decide)) (append (widen s17952_32 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_16 (by decide)) (widen s23888_1 (by decide)))))))))))))))

theorem claim556 : CheckedClaim verifiedRow ⟨1,1,2,17956,19944,530551736065,1030156509437⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17956 1989 ⟨530552004620,1030156240882⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))

theorem claim557 : CheckedClaim verifiedRow ⟨1,1,2,17956,21932,530551736065,1675536299576⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17956 3977 ⟨530552004620,1675536031021⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_32 (by decide)) (append (widen s21920_8 (by decide)) (append (widen s21928_4 (by decide)) (widen s21932_1 (by decide)))))))))))))))

theorem claim558 : CheckedClaim verifiedRow ⟨1,1,2,17956,23920,530551736065,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17956 5965 ⟨530552004620,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))))))

theorem claim559 : CheckedClaim verifiedRow ⟨1,1,2,17988,19976,536158419808,1040273265010⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17988 1989 ⟨536158688363,1040272996455⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide)))))))))))

theorem claim560 : CheckedClaim verifiedRow ⟨1,1,2,17988,21964,536158419808,1684769291906⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17988 3977 ⟨536158688363,1684769023351⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide)))))))))))))))

theorem claim561 : CheckedClaim verifiedRow ⟨1,1,2,17988,23952,536158419808,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 17988 5965 ⟨536158688363,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide))))))))))))))

theorem claim562 : CheckedClaim verifiedRow ⟨1,1,2,18020,20008,541853166906,1050434560941⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 18020 1989 ⟨541853435461,1050434292386⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim563 : CheckedClaim verifiedRow ⟨1,1,2,18020,21996,541853166906,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 18020 3977 ⟨541853435461,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide)))))))))))))))

theorem claim564 : CheckedClaim verifiedRow ⟨1,1,2,18020,23984,541853166906,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 18020 5965 ⟨541853435461,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_2048 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))))

theorem claim565 : CheckedClaim verifiedRow ⟨1,1,2,18052,20040,547635754367,1060639023273⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 18052 1989 ⟨547636022922,1060638754718⟩
  rw [← get_eq_raw]
  exact (append (widen s18052_4 (by decide)) (append (widen s18056_8 (by decide)) (append (widen s18064_16 (by decide)) (append (widen s18080_32 (by decide)) (append (widen s18112_64 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide))))))))))))

theorem claim566 : CheckedClaim verifiedRow ⟨1,1,2,19014,21996,760900168478,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19014 2983 ⟨760900437033,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s19014_2 (by decide)) (append (widen s19016_8 (by decide)) (append (widen s19024_16 (by decide)) (append (widen s19040_32 (by decide)) (append (widen s19072_128 (by decide)) (append (widen s19200_256 (by decide)) (append (widen s19456_1024 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide))))))))))))))))

theorem claim567 : CheckedClaim verifiedRow ⟨1,1,2,19912,25876,1020085104853,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19912 5965 ⟨1020085373408,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19912_8 (by decide)) (append (widen s19920_16 (by decide)) (append (widen s19936_32 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_16 (by decide)) (append (widen s25872_4 (by decide)) (widen s25876_1 (by decide)))))))))))

theorem claim568 : CheckedClaim verifiedRow ⟨1,1,2,19944,23920,1030155972324,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19944 3977 ⟨1030156240879,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))

theorem claim569 : CheckedClaim verifiedRow ⟨1,1,2,19944,25908,1030155972324,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19944 5965 ⟨1030156240879,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_32 (by decide)) (append (widen s25888_16 (by decide)) (append (widen s25904_4 (by decide)) (widen s25908_1 (by decide)))))))))))

theorem claim570 : CheckedClaim verifiedRow ⟨1,1,2,19944,27896,-846552384897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19944 7953 ⟨-846552116342,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide)))))))))))))

theorem claim571 : CheckedClaim verifiedRow ⟨1,1,2,19976,21964,1040272727897,1684769291906⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19976 1989 ⟨1040272996452,1684769023351⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide))))))))))))))

theorem claim572 : CheckedClaim verifiedRow ⟨1,1,2,19976,23952,1040272727897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19976 3977 ⟨1040272996452,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide)))))))))))))

theorem claim573 : CheckedClaim verifiedRow ⟨1,1,2,19976,25940,1040272727897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19976 5965 ⟨1040272996452,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_16 (by decide)) (append (widen s25936_4 (by decide)) (widen s25940_1 (by decide))))))))))))))

theorem claim574 : CheckedClaim verifiedRow ⟨1,1,2,19976,27928,-885965123042,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19976 7953 ⟨-885964854487,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide))))))))))))))

private theorem s27648_512 : Run get 27648 512 ⟨-1173163257451,-545316336133⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨-1816445198791,-1174414763642⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨-1816445198791,-545316336133⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨-1816445198791,571962933466⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨-1816445198791,1842551736188⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨-2445174200216,-1817697083165⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨-3029221074167,-2446368302258⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨-3029221074167,-1817697083165⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

private theorem s29696_512 : Run get 29696 512 ⟨-3539109737013,-3030298514738⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨-3948083105514,-3540014939336⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨-3948083105514,-3030298514738⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨-3948083105514,-1817697083165⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨-4234058663307,-3948767783307⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨-4381290940152,-4234485410627⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨-4381290940152,-3948767783307⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim575 : CheckedClaim verifiedRow ⟨1,1,2,19976,31904,-4397386993392,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 19976 11929 ⟨-4397386724837,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide))))))))))))))

theorem claim576 : CheckedClaim verifiedRow ⟨1,1,2,20008,21996,1050434023828,1693909942306⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 20008 1989 ⟨1050434292383,1693909673751⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide))))))))))))))

theorem claim577 : CheckedClaim verifiedRow ⟨1,1,2,20008,23984,1050434023828,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 20008 3977 ⟨1050434292383,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide)))))))))))))

theorem claim578 : CheckedClaim verifiedRow ⟨1,1,2,20008,25972,1050434023828,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 20008 5965 ⟨1050434292383,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_32 (by decide)) (append (widen s25952_16 (by decide)) (append (widen s25968_4 (by decide)) (widen s25972_1 (by decide))))))))))))))

theorem claim579 : CheckedClaim verifiedRow ⟨1,1,2,20008,27960,-925481865997,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 20008 7953 ⟨-925481597442,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_4096 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide))))))))))))))

theorem claim580 : CheckedClaim verifiedRow ⟨1,1,2,20040,22028,1060638486160,1702955267462⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 20040 1989 ⟨1060638754715,1702954998907⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_512 (by decide)) (append (widen s22016_8 (by decide)) (append (widen s22024_4 (by decide)) (widen s22028_1 (by decide)))))))))))

theorem claim581 : CheckedClaim verifiedRow ⟨1,1,2,20040,24016,1060638486160,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 20040 3977 ⟨1060638754715,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim582 : CheckedClaim verifiedRow ⟨1,1,2,20938,23920,1358129634721,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 20938 2983 ⟨1358129903276,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s20938_2 (by decide)) (append (widen s20940_4 (by decide)) (append (widen s20944_16 (by decide)) (append (widen s20960_32 (by decide)) (append (widen s20992_512 (by decide)) (append (widen s21504_1024 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))))

theorem claim583 : CheckedClaim verifiedRow ⟨1,1,2,21932,24914,1675535762463,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 21932 2983 ⟨1675536031018,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s21932_4 (by decide)) (append (widen s21936_16 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_256 (by decide)) (append (widen s24832_64 (by decide)) (append (widen s24896_16 (by decide)) (append (widen s24912_2 (by decide)) (widen s24914_1 (by decide)))))))))))

theorem claim584 : CheckedClaim verifiedRow ⟨1,1,2,21932,25908,1178903421211,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 21932 3977 ⟨1178903689766,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s21932_4 (by decide)) (append (widen s21936_16 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_32 (by decide)) (append (widen s25888_16 (by decide)) (append (widen s25904_4 (by decide)) (widen s25908_1 (by decide))))))))))))

theorem claim585 : CheckedClaim verifiedRow ⟨1,1,2,21932,27896,-846552384897,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 21932 5965 ⟨-846552116342,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s21932_4 (by decide)) (append (widen s21936_16 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide))))))))))))))

theorem claim586 : CheckedClaim verifiedRow ⟨1,1,2,21964,27928,-885965123042,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 21964 5965 ⟨-885964854487,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s21964_4 (by decide)) (append (widen s21968_16 (by decide)) (append (widen s21984_32 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide))))))))))))

theorem claim587 : CheckedClaim verifiedRow ⟨1,1,2,21996,23984,1693909405193,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 21996 1989 ⟨1693909673748,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s21996_4 (by decide)) (append (widen s22000_16 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))

theorem claim588 : CheckedClaim verifiedRow ⟨1,1,2,21996,27960,-925481865997,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 21996 5965 ⟨-925481597442,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s21996_4 (by decide)) (append (widen s22000_16 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_2048 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide))))))))))))

theorem claim589 : CheckedClaim verifiedRow ⟨1,1,2,22028,24016,1702954730349,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 22028 1989 ⟨1702954998904,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s22028_4 (by decide)) (append (widen s22032_16 (by decide)) (append (widen s22048_32 (by decide)) (append (widen s22080_64 (by decide)) (append (widen s22144_128 (by decide)) (append (widen s22272_256 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim590 : CheckedClaim verifiedRow ⟨1,1,2,22926,25908,1178903421211,1964161974401⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 22926 2983 ⟨1178903689766,1964161705846⟩
  rw [← get_eq_raw]
  exact (append (widen s22926_2 (by decide)) (append (widen s22928_16 (by decide)) (append (widen s22944_32 (by decide)) (append (widen s22976_64 (by decide)) (append (widen s23040_512 (by decide)) (append (widen s23552_1024 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_32 (by decide)) (append (widen s25888_16 (by decide)) (append (widen s25904_4 (by decide)) (widen s25908_1 (by decide)))))))))))))

theorem claim591 : CheckedClaim verifiedRow ⟨1,1,2,23888,27864,-807249985179,1956302336842⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23888 3977 ⟨-807249716624,1956302068287⟩
  rw [← get_eq_raw]
  exact (append (widen s23888_16 (by decide)) (append (widen s23904_32 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_16 (by decide)) (append (widen s27856_8 (by decide)) (widen s27864_1 (by decide))))))))))))

theorem claim592 : CheckedClaim verifiedRow ⟨1,1,2,23888,29852,-3194768064268,1956302336842⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23888 5965 ⟨-3194767795713,1956302068287⟩
  rw [← get_eq_raw]
  exact (append (widen s23888_16 (by decide)) (append (widen s23904_32 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_16 (by decide)) (append (widen s29840_8 (by decide)) (append (widen s29848_4 (by decide)) (widen s29852_1 (by decide))))))))))))

theorem claim593 : CheckedClaim verifiedRow ⟨1,1,2,23888,31840,-4392743487380,1956302336842⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23888 7953 ⟨-4392743218825,1956302068287⟩
  rw [← get_eq_raw]
  exact (append (widen s23888_16 (by decide)) (append (widen s23904_32 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_64 (by decide)) (append (widen s31808_32 (by decide)) (widen s31840_1 (by decide)))))))))))

theorem claim594 : CheckedClaim verifiedRow ⟨1,1,2,23920,27896,-846552384897,1954088134584⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23920 3977 ⟨-846552116342,1954087866029⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide))))))))))))

theorem claim595 : CheckedClaim verifiedRow ⟨1,1,2,23920,29884,-3227578549738,1954088134584⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23920 5965 ⟨-3227578281183,1954087866029⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_32 (by decide)) (append (widen s29856_16 (by decide)) (append (widen s29872_8 (by decide)) (append (widen s29880_4 (by decide)) (widen s29884_1 (by decide))))))))))))

theorem claim596 : CheckedClaim verifiedRow ⟨1,1,2,23952,29916,-3260057981765,1951590456250⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23952 5965 ⟨-3260057713210,1951590187695⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_64 (by decide)) (append (widen s29888_16 (by decide)) (append (widen s29904_8 (by decide)) (append (widen s29912_4 (by decide)) (widen s29916_1 (by decide)))))))))))))

theorem claim597 : CheckedClaim verifiedRow ⟨1,1,2,23984,25972,1131528135180,1948806565392⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23984 1989 ⟨1131528403735,1948806296837⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_32 (by decide)) (append (widen s25952_16 (by decide)) (append (widen s25968_4 (by decide)) (widen s25972_1 (by decide)))))))))))

theorem claim598 : CheckedClaim verifiedRow ⟨1,1,2,23984,27960,-925481865997,1948806565392⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 23984 3977 ⟨-925481597442,1948806296837⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim599 : CheckedClaim verifiedRow ⟨1,1,2,24016,27992,-965096221625,1945733758896⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 24016 3977 ⟨-965095953070,1945733490341⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide)))))))))))

theorem claim600 : CheckedClaim verifiedRow ⟨1,1,2,24016,31968,-4399709768237,1945733758896⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 24016 7953 ⟨-4399709499682,1945733490341⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim601 : CheckedClaim verifiedRow ⟨1,1,2,25876,29852,-3194768064268,1202065709959⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 25876 3977 ⟨-3194767795713,1202065441404⟩
  rw [← get_eq_raw]
  exact (append (widen s25876_4 (by decide)) (append (widen s25880_8 (by decide)) (append (widen s25888_32 (by decide)) (append (widen s25920_64 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_16 (by decide)) (append (widen s29840_8 (by decide)) (append (widen s29848_4 (by decide)) (widen s29852_1 (by decide))))))))))))))

theorem claim602 : CheckedClaim verifiedRow ⟨1,1,2,25876,31840,-4392743487380,1202065709959⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 25876 5965 ⟨-4392743218825,1202065441404⟩
  rw [← get_eq_raw]
  exact (append (widen s25876_4 (by decide)) (append (widen s25880_8 (by decide)) (append (widen s25888_32 (by decide)) (append (widen s25920_64 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_64 (by decide)) (append (widen s31808_32 (by decide)) (widen s31840_1 (by decide)))))))))))))

theorem claim603 : CheckedClaim verifiedRow ⟨1,1,2,25908,29884,-3227578549738,1178903958324⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 25908 3977 ⟨-3227578281183,1178903689769⟩
  rw [← get_eq_raw]
  exact (append (widen s25908_4 (by decide)) (append (widen s25912_8 (by decide)) (append (widen s25920_64 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_32 (by decide)) (append (widen s29856_16 (by decide)) (append (widen s29872_8 (by decide)) (append (widen s29880_4 (by decide)) (widen s29884_1 (by decide))))))))))))))

theorem claim604 : CheckedClaim verifiedRow ⟨1,1,2,25940,28922,-2128349641443,1155391209848⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 25940 2983 ⟨-2128349372888,1155390941293⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_128 (by decide)) (append (widen s28800_64 (by decide)) (append (widen s28864_32 (by decide)) (append (widen s28896_16 (by decide)) (append (widen s28912_8 (by decide)) (append (widen s28920_2 (by decide)) (widen s28922_1 (by decide))))))))))))))

theorem claim605 : CheckedClaim verifiedRow ⟨1,1,2,25940,29916,-3260057981765,1155391209848⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 25940 3977 ⟨-3260057713210,1155390941293⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_64 (by decide)) (append (widen s29888_16 (by decide)) (append (widen s29904_8 (by decide)) (append (widen s29912_4 (by decide)) (widen s29916_1 (by decide))))))))))))))

theorem claim606 : CheckedClaim verifiedRow ⟨1,1,2,25940,31904,-4397386993392,1155391209848⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 25940 5965 ⟨-4397386724837,1155390941293⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_2048 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide))))))))))))

theorem claim607 : CheckedClaim verifiedRow ⟨1,1,2,26004,27992,-965096221625,1107317640889⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 26004 1989 ⟨-965095953070,1107317372334⟩
  rw [← get_eq_raw]
  exact (append (widen s26004_4 (by decide)) (append (widen s26008_8 (by decide)) (append (widen s26016_32 (by decide)) (append (widen s26048_64 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide))))))))))))

theorem claim608 : CheckedClaim verifiedRow ⟨1,1,2,26934,29916,-3260057981765,260540266655⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 26934 2983 ⟨-3260057713210,260539998100⟩
  rw [← get_eq_raw]
  exact (append (widen s26934_2 (by decide)) (append (widen s26936_8 (by decide)) (append (widen s26944_64 (by decide)) (append (widen s27008_128 (by decide)) (append (widen s27136_512 (by decide)) (append (widen s27648_1024 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_64 (by decide)) (append (widen s29888_16 (by decide)) (append (widen s29904_8 (by decide)) (append (widen s29912_4 (by decide)) (widen s29916_1 (by decide))))))))))))))

theorem claim609 : CheckedClaim verifiedRow ⟨1,1,2,27928,31904,-4397386993392,-885964585929⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 27928 3977 ⟨-4397386724837,-885964854484⟩
  rw [← get_eq_raw]
  exact (append (widen s27928_8 (by decide)) (append (widen s27936_32 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide)))))))))))

theorem claim610 : CheckedClaim verifiedRow ⟨1,1,2,27992,31968,-4399709768237,-965095684512⟩ := by
  change Run (rawBlock verifiedRow 1 1 .second) 27992 3977 ⟨-4399709499682,-965095953067⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
