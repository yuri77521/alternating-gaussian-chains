import Point22AtlasRangeGroup212Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf212

private abbrev get := fastBlock verifiedRow 2 1 .second
private theorem get_eq_raw : get = rawBlock verifiedRow 2 1 .second :=
  funext (fastBlock_eq_raw verifiedRow 2 1 .second)

private theorem s512_512 : Run get 512 512 ⟨8923310573,17623278949⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

theorem claim725 : CheckedClaim verifiedRow ⟨2,1,2,64,1058,870583302,18189290188⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 64 995 ⟨871120412,18188753078⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_32 (by decide)) (append (widen s1056_2 (by decide)) (widen s1058_1 (by decide))))))))

private theorem s1024_512 : Run get 1024 512 ⟨17639499448,25369196766⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

private theorem s1536_512 : Run get 1536 512 ⟨25383097940,31742933745⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨17639499448,31742933745⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

theorem claim726 : CheckedClaim verifiedRow ⟨2,1,2,64,2052,870583302,31797872271⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 64 1989 ⟨871120412,31797335161⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide))))))))

private theorem s2048_512 : Run get 2048 512 ⟨31753826843,36447518684⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

private theorem s2560_512 : Run get 2560 512 ⟨36454939003,39308227572⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨31753826843,39308227572⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨39311960168,40279896490⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

theorem claim727 : CheckedClaim verifiedRow ⟨2,1,2,64,4040,870583302,40280965611⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 64 3977 ⟨871120412,40280428501⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))

theorem claim728 : CheckedClaim verifiedRow ⟨2,1,2,96,2084,1451117317,32142233958⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 96 1989 ⟨1451654427,32141696848⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_32 (by decide)) (append (widen s2080_4 (by decide)) (widen s2084_1 (by decide)))))))))

theorem claim729 : CheckedClaim verifiedRow ⟨2,1,2,96,4072,1451117317,40280965611⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 96 3977 ⟨1451654427,40280428501⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide))))))))))))))

private theorem s3584_512 : Run get 3584 512 ⟨39442632211,40280428501⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨39311960168,40280428501⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

private theorem s2048_2048 : Run get 2048 2048 ⟨31753826843,40280428501⟩ :=
  join s2048_1024 s3072_1024 (by decide) (by decide)

theorem claim730 : CheckedClaim verifiedRow ⟨2,1,2,128,4104,2031332006,40280965611⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 128 3977 ⟨2031869116,40280428501⟩
  rw [← get_eq_raw]
  exact (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_8 (by decide)) (widen s4104_1 (by decide))))))))

theorem claim731 : CheckedClaim verifiedRow ⟨2,1,2,1058,2052,18188215962,31797872271⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 1058 995 ⟨18188753072,31797335161⟩
  rw [← get_eq_raw]
  exact (append (widen s1058_2 (by decide)) (append (widen s1060_4 (by decide)) (append (widen s1064_8 (by decide)) (append (widen s1072_16 (by decide)) (append (widen s1088_64 (by decide)) (append (widen s1152_128 (by decide)) (append (widen s1280_256 (by decide)) (append (widen s1536_512 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide)))))))))))

theorem claim732 : CheckedClaim verifiedRow ⟨2,1,2,2052,3046,31796798045,39213094214⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 2052 995 ⟨31797335155,39212557104⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_256 (by decide)) (append (widen s2816_128 (by decide)) (append (widen s2944_64 (by decide)) (append (widen s3008_32 (by decide)) (append (widen s3040_4 (by decide)) (append (widen s3044_2 (by decide)) (widen s3046_1 (by decide)))))))))))))))

theorem claim733 : CheckedClaim verifiedRow ⟨2,1,2,2052,4040,31796798045,40280965611⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 2052 1989 ⟨31797335155,40280428501⟩
  rw [← get_eq_raw]
  exact (append (widen s2052_4 (by decide)) (append (widen s2056_8 (by decide)) (append (widen s2064_16 (by decide)) (append (widen s2080_32 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide)))))))))))))))

theorem claim734 : CheckedClaim verifiedRow ⟨2,1,2,2084,4072,32141159732,40280965611⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 2084 1989 ⟨32141696842,40280428501⟩
  rw [← get_eq_raw]
  exact (append (widen s2084_4 (by decide)) (append (widen s2088_8 (by decide)) (append (widen s2096_16 (by decide)) (append (widen s2112_64 (by decide)) (append (widen s2176_128 (by decide)) (append (widen s2304_256 (by decide)) (append (widen s2560_512 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_32 (by decide)) (append (widen s4064_8 (by decide)) (widen s4072_1 (by decide)))))))))))))))

theorem claim735 : CheckedClaim verifiedRow ⟨2,1,2,3046,4040,39212019988,40280965611⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 3046 995 ⟨39212557098,40280428501⟩
  rw [← get_eq_raw]
  exact (append (widen s3046_2 (by decide)) (append (widen s3048_8 (by decide)) (append (widen s3056_16 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_64 (by decide)) (append (widen s4032_8 (by decide)) (widen s4040_1 (by decide))))))))))

private theorem s4096_512 : Run get 4096 512 ⟨36987026160,39439335436⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

private theorem s4608_512 : Run get 4608 512 ⟨33191030950,36980816494⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨33191030950,39439335436⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨28391386078,33182518671⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

theorem claim736 : CheckedClaim verifiedRow ⟨2,1,2,4040,6028,24210494291,39614892741⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 4040 1989 ⟨24211031401,39614355631⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_8 (by decide)) (append (widen s6024_4 (by decide)) (widen s6028_1 (by decide)))))))))))

private theorem s5632_512 : Run get 5632 512 ⟨22952811443,28381266329⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨22952811443,33182518671⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨22952811443,39439335436⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨17238116711,22941803998⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨11581947796,17226910351⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨11581947796,22941803998⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨6270200387,11571154060⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim737 : CheckedClaim verifiedRow ⟨2,1,2,4040,8016,3072269383,39614892741⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 4040 3977 ⟨3072806493,39614355631⟩
  rw [← get_eq_raw]
  exact (append (widen s4040_8 (by decide)) (append (widen s4048_16 (by decide)) (append (widen s4064_32 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim738 : CheckedClaim verifiedRow ⟨2,1,2,4072,5066,33636087441,39517280068⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 4072 995 ⟨33636624551,39516742958⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_512 (by decide)) (append (widen s4608_256 (by decide)) (append (widen s4864_128 (by decide)) (append (widen s4992_64 (by decide)) (append (widen s5056_8 (by decide)) (append (widen s5064_2 (by decide)) (widen s5066_1 (by decide))))))))))

theorem claim739 : CheckedClaim verifiedRow ⟨2,1,2,4072,6060,23862000442,39517280068⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 4072 1989 ⟨23862537552,39516742958⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_1024 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_32 (by decide)) (append (widen s6048_8 (by decide)) (append (widen s6056_4 (by decide)) (widen s6060_1 (by decide)))))))))))

theorem claim740 : CheckedClaim verifiedRow ⟨2,1,2,4072,8048,2783353745,39517280068⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 4072 3977 ⟨2783890855,39516742958⟩
  rw [← get_eq_raw]
  exact (append (widen s4072_8 (by decide)) (append (widen s4080_16 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim741 : CheckedClaim verifiedRow ⟨2,1,2,4104,6092,23512211363,39413275258⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 4104 1989 ⟨23512748473,39412738148⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_512 (by decide)) (append (widen s5632_256 (by decide)) (append (widen s5888_128 (by decide)) (append (widen s6016_64 (by decide)) (append (widen s6080_8 (by decide)) (append (widen s6088_4 (by decide)) (widen s6092_1 (by decide)))))))))))))))

theorem claim742 : CheckedClaim verifiedRow ⟨2,1,2,4104,8080,2497141221,39413275258⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 4104 3977 ⟨2497678331,39412738148⟩
  rw [← get_eq_raw]
  exact (append (widen s4104_8 (by decide)) (append (widen s4112_16 (by decide)) (append (widen s4128_32 (by decide)) (append (widen s4160_64 (by decide)) (append (widen s4224_128 (by decide)) (append (widen s4352_256 (by decide)) (append (widen s4608_512 (by decide)) (append (widen s5120_1024 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide)))))))))))))))

theorem claim743 : CheckedClaim verifiedRow ⟨2,1,2,6028,8016,3072269383,24211568517⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 6028 1989 ⟨3072806493,24211031407⟩
  rw [← get_eq_raw]
  exact (append (widen s6028_4 (by decide)) (append (widen s6032_16 (by decide)) (append (widen s6048_32 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide)))))))))))

theorem claim744 : CheckedClaim verifiedRow ⟨2,1,2,6060,8048,2783353745,23863074668⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 6060 1989 ⟨2783890855,23862537558⟩
  rw [← get_eq_raw]
  exact (append (widen s6060_4 (by decide)) (append (widen s6064_16 (by decide)) (append (widen s6080_64 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))

theorem claim745 : CheckedClaim verifiedRow ⟨2,1,2,6092,8080,2497141221,23513285589⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 6092 1989 ⟨2497678331,23512748479⟩
  rw [← get_eq_raw]
  exact (append (widen s6092_4 (by decide)) (append (widen s6096_16 (by decide)) (append (widen s6112_32 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide))))))))))

private theorem s8192_512 : Run get 8192 512 ⟨-2495391421,1517693121⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

private theorem s8704_512 : Run get 8704 512 ⟨-5709303410,-2502472925⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨-5709303410,1517693121⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨-8092914152,-5714766093⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

theorem claim746 : CheckedClaim verifiedRow ⟨2,1,2,8016,10004,-9045862269,3073343609⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 8016 1989 ⟨-9045325159,3072806499⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_16 (by decide)) (append (widen s10000_4 (by decide)) (widen s10004_1 (by decide))))))))))

private theorem s9728_512 : Run get 9728 512 ⟨-9676679315,-8096769643⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨-9676679315,-5714766093⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨-9676679315,1517693121⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨-10531464837,-9679030984⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨-10757948986,-10532481811⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨-10757948986,-9679030984⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨-10754908449,-10458880343⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

theorem claim747 : CheckedClaim verifiedRow ⟨2,1,2,8016,11992,-10758486096,3073343609⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 8016 3977 ⟨-10757948986,3072806499⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide))))))))))))

theorem claim748 : CheckedClaim verifiedRow ⟨2,1,2,8048,10036,-9141187513,2784427971⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 8048 1989 ⟨-9140650403,2783890861⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_32 (by decide)) (append (widen s10016_16 (by decide)) (append (widen s10032_4 (by decide)) (widen s10036_1 (by decide))))))))))

theorem claim749 : CheckedClaim verifiedRow ⟨2,1,2,8048,12024,-10758486096,2784427971⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 8048 3977 ⟨-10757948986,2783890861⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide))))))))))))

theorem claim750 : CheckedClaim verifiedRow ⟨2,1,2,8080,10068,-9233529443,2498215447⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 8080 1989 ⟨-9232992333,2497678337⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_1024 (by decide)) (append (widen s9216_512 (by decide)) (append (widen s9728_256 (by decide)) (append (widen s9984_64 (by decide)) (append (widen s10048_16 (by decide)) (append (widen s10064_4 (by decide)) (widen s10068_1 (by decide)))))))))))

theorem claim751 : CheckedClaim verifiedRow ⟨2,1,2,8080,12056,-10758486096,2498215447⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 8080 3977 ⟨-10757948986,2497678337⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_2048 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

theorem claim752 : CheckedClaim verifiedRow ⟨2,1,2,10004,11992,-10758486096,-9044788043⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 10004 1989 ⟨-10757948986,-9045325153⟩
  rw [← get_eq_raw]
  exact (append (widen s10004_4 (by decide)) (append (widen s10008_8 (by decide)) (append (widen s10016_32 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_16 (by decide)) (append (widen s11984_8 (by decide)) (widen s11992_1 (by decide)))))))))))))

theorem claim753 : CheckedClaim verifiedRow ⟨2,1,2,10036,12024,-10758486096,-9140113287⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 10036 1989 ⟨-10757948986,-9140650397⟩
  rw [← get_eq_raw]
  exact (append (widen s10036_4 (by decide)) (append (widen s10040_8 (by decide)) (append (widen s10048_64 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_128 (by decide)) (append (widen s11904_64 (by decide)) (append (widen s11968_32 (by decide)) (append (widen s12000_16 (by decide)) (append (widen s12016_8 (by decide)) (widen s12024_1 (by decide)))))))))))))

theorem claim754 : CheckedClaim verifiedRow ⟨2,1,2,10068,12056,-10758486096,-9232455217⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 10068 1989 ⟨-10757948986,-9232992327⟩
  rw [← get_eq_raw]
  exact (append (widen s10068_4 (by decide)) (append (widen s10072_8 (by decide)) (append (widen s10080_32 (by decide)) (append (widen s10112_128 (by decide)) (append (widen s10240_1024 (by decide)) (append (widen s11264_512 (by decide)) (append (widen s11776_256 (by decide)) (append (widen s12032_16 (by decide)) (append (widen s12048_8 (by decide)) (widen s12056_1 (by decide)))))))))))

private theorem s12288_512 : Run get 12288 512 ⟨-9755138861,-8755610430⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨-8753425618,-7548214727⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨-9755138861,-7548214727⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨-7545707094,-6209984849⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

theorem claim755 : CheckedClaim verifiedRow ⟨2,1,2,11992,13980,-10204999445,-5782050348⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 11992 1989 ⟨-10204462335,-5782587458⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_16 (by decide)) (append (widen s13968_8 (by decide)) (append (widen s13976_4 (by decide)) (widen s13980_1 (by decide)))))))))))

private theorem s13824_512 : Run get 13824 512 ⟨-6207282929,-4797163144⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨-7545707094,-4797163144⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨-9755138861,-4797163144⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨-4794358297,-3347687273⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨-3344837126,-1883776049⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨-4794358297,-1883776049⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨-1880911010,-415869486⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim756 : CheckedClaim verifiedRow ⟨2,1,2,11992,15968,-10204999445,-137131330⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 11992 3977 ⟨-10204462335,-137668440⟩
  rw [← get_eq_raw]
  exact (append (widen s11992_8 (by decide)) (append (widen s12000_32 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim757 : CheckedClaim verifiedRow ⟨2,1,2,12024,14012,-10161833044,-5694209985⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 12024 1989 ⟨-10161295934,-5694747095⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_32 (by decide)) (append (widen s13984_16 (by decide)) (append (widen s14000_8 (by decide)) (append (widen s14008_4 (by decide)) (widen s14012_1 (by decide)))))))))))

theorem claim758 : CheckedClaim verifiedRow ⟨2,1,2,12024,16000,-10161833044,-45352415⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 12024 3977 ⟨-10161295934,-45889525⟩
  rw [← get_eq_raw]
  exact (append (widen s12024_8 (by decide)) (append (widen s12032_256 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim759 : CheckedClaim verifiedRow ⟨2,1,2,12056,14044,-10117292686,-5606146630⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 12056 1989 ⟨-10116755576,-5606683740⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_1024 (by decide)) (append (widen s13312_512 (by decide)) (append (widen s13824_128 (by decide)) (append (widen s13952_64 (by decide)) (append (widen s14016_16 (by decide)) (append (widen s14032_8 (by decide)) (append (widen s14040_4 (by decide)) (widen s14044_1 (by decide)))))))))))))

theorem claim760 : CheckedClaim verifiedRow ⟨2,1,2,12056,16032,-10117292686,46426641⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 12056 3977 ⟨-10116755576,45889531⟩
  rw [← get_eq_raw]
  exact (append (widen s12056_8 (by decide)) (append (widen s12064_32 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim761 : CheckedClaim verifiedRow ⟨2,1,2,12088,16064,-10071404584,138205556⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 12088 3977 ⟨-10070867474,137668446⟩
  rw [← get_eq_raw]
  exact (append (widen s12088_8 (by decide)) (append (widen s12096_64 (by decide)) (append (widen s12160_128 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim762 : CheckedClaim verifiedRow ⟨2,1,2,13980,15968,-5783124574,-137131330⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 13980 1989 ⟨-5782587464,-137668440⟩
  rw [← get_eq_raw]
  exact (append (widen s13980_4 (by decide)) (append (widen s13984_32 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide))))))))))

theorem claim763 : CheckedClaim verifiedRow ⟨2,1,2,14012,16000,-5695284211,-45352415⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 14012 1989 ⟨-5694747101,-45889525⟩
  rw [← get_eq_raw]
  exact (append (widen s14012_4 (by decide)) (append (widen s14016_64 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))

theorem claim764 : CheckedClaim verifiedRow ⟨2,1,2,14044,16032,-5607220856,46426641⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 14044 1989 ⟨-5606683746,45889531⟩
  rw [← get_eq_raw]
  exact (append (widen s14044_4 (by decide)) (append (widen s14048_32 (by decide)) (append (widen s14080_256 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))

private theorem s16384_512 : Run get 16384 512 ⟨1055379727,2519405316⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨2522266201,3978927208⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨1055379727,3978927208⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨3981762783,5416083276⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

theorem claim765 : CheckedClaim verifiedRow ⟨2,1,2,15968,17956,-138205556,5518944121⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 15968 1989 ⟨-137668446,5518407011⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_32 (by decide)) (append (widen s17952_4 (by decide)) (widen s17956_1 (by decide)))))))))

private theorem s17920_512 : Run get 17920 512 ⟨5418852242,6802253677⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨3981762783,6802253677⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨1055379727,6802253677⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨6804884354,8091786116⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨8094171165,9220135321⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨6804884354,9220135321⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

theorem claim766 : CheckedClaim verifiedRow ⟨2,1,2,15968,19944,-138205556,10071404584⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 15968 3977 ⟨-137668446,10070867474⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))

theorem claim767 : CheckedClaim verifiedRow ⟨2,1,2,16000,17988,-46426641,5607220856⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 16000 1989 ⟨-45889531,5606683746⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_4 (by decide)) (widen s17988_1 (by decide))))))))

private theorem s19456_512 : Run get 19456 512 ⟨9222129906,10103984643⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

theorem claim768 : CheckedClaim verifiedRow ⟨2,1,2,16000,19976,-46426641,10117292686⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 16000 3977 ⟨-45889531,10116755576⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide))))))))

theorem claim769 : CheckedClaim verifiedRow ⟨2,1,2,16032,18020,45352415,5695284211⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 16032 1989 ⟨45889525,5694747101⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_1024 (by decide)) (append (widen s17408_512 (by decide)) (append (widen s17920_64 (by decide)) (append (widen s17984_32 (by decide)) (append (widen s18016_4 (by decide)) (widen s18020_1 (by decide))))))))))

theorem claim770 : CheckedClaim verifiedRow ⟨2,1,2,16032,20008,45352415,10161833044⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 16032 3977 ⟨45889525,10161295934⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide))))))))))

private theorem s19968_512 : Run get 19968 512 ⟨10105408876,10643733555⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨9222129906,10643733555⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨6804884354,10643733555⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨1055379727,10643733555⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨10644379871,10757948986⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨10244541415,10728264290⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨10244541415,10757948986⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

private theorem s21504_512 : Run get 21504 512 ⟨9084412022,10242967024⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨7160477085,9081422906⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨7160477085,10242967024⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨7160477085,10757948986⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨4417751877,7155929471⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨847322790,4411579285⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨847322790,7155929471⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

theorem claim771 : CheckedClaim verifiedRow ⟨2,1,2,16032,23984,-2784427971,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 16032 7953 ⟨-2783890861,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))

theorem claim772 : CheckedClaim verifiedRow ⟨2,1,2,16064,20040,137131330,10204999445⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 16064 3977 ⟨137668440,10204462335⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_2048 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_64 (by decide)) (append (widen s20032_8 (by decide)) (widen s20040_1 (by decide)))))))))

theorem claim773 : CheckedClaim verifiedRow ⟨2,1,2,17956,19944,5517869895,10071404584⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 17956 1989 ⟨5518407005,10070867474⟩
  rw [← get_eq_raw]
  exact (append (widen s17956_4 (by decide)) (append (widen s17960_8 (by decide)) (append (widen s17968_16 (by decide)) (append (widen s17984_64 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_256 (by decide)) (append (widen s19712_128 (by decide)) (append (widen s19840_64 (by decide)) (append (widen s19904_32 (by decide)) (append (widen s19936_8 (by decide)) (widen s19944_1 (by decide))))))))))))))

theorem claim774 : CheckedClaim verifiedRow ⟨2,1,2,17988,19976,5606146630,10117292686⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 17988 1989 ⟨5606683740,10116755576⟩
  rw [← get_eq_raw]
  exact (append (widen s17988_4 (by decide)) (append (widen s17992_8 (by decide)) (append (widen s18000_16 (by decide)) (append (widen s18016_32 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_8 (by decide)) (widen s19976_1 (by decide)))))))))))

theorem claim775 : CheckedClaim verifiedRow ⟨2,1,2,18020,20008,5694209985,10161833044⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 18020 1989 ⟨5694747095,10161295934⟩
  rw [← get_eq_raw]
  exact (append (widen s18020_4 (by decide)) (append (widen s18024_8 (by decide)) (append (widen s18032_16 (by decide)) (append (widen s18048_128 (by decide)) (append (widen s18176_256 (by decide)) (append (widen s18432_1024 (by decide)) (append (widen s19456_512 (by decide)) (append (widen s19968_32 (by decide)) (append (widen s20000_8 (by decide)) (widen s20008_1 (by decide)))))))))))

theorem claim776 : CheckedClaim verifiedRow ⟨2,1,2,19944,21932,9321832628,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 19944 1989 ⟨9322369738,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_32 (by decide)) (append (widen s21920_8 (by decide)) (append (widen s21928_4 (by decide)) (widen s21932_1 (by decide)))))))))))

theorem claim777 : CheckedClaim verifiedRow ⟨2,1,2,19944,23920,-2214739371,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 19944 3977 ⟨-2214202261,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s19944_8 (by decide)) (append (widen s19952_16 (by decide)) (append (widen s19968_512 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))

theorem claim778 : CheckedClaim verifiedRow ⟨2,1,2,19976,21964,9232455217,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 19976 1989 ⟨9232992327,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_8 (by decide)) (append (widen s21960_4 (by decide)) (widen s21964_1 (by decide))))))))))))))

theorem claim779 : CheckedClaim verifiedRow ⟨2,1,2,19976,23952,-2498215447,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 19976 3977 ⟨-2497678337,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s19976_8 (by decide)) (append (widen s19984_16 (by decide)) (append (widen s20000_32 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide)))))))))))))

theorem claim780 : CheckedClaim verifiedRow ⟨2,1,2,20008,21996,9140113287,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 20008 1989 ⟨9140650397,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_1024 (by decide)) (append (widen s21504_256 (by decide)) (append (widen s21760_128 (by decide)) (append (widen s21888_64 (by decide)) (append (widen s21952_32 (by decide)) (append (widen s21984_8 (by decide)) (append (widen s21992_4 (by decide)) (widen s21996_1 (by decide))))))))))))))

theorem claim781 : CheckedClaim verifiedRow ⟨2,1,2,20008,23984,-2784427971,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 20008 3977 ⟨-2783890861,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s20008_8 (by decide)) (append (widen s20016_16 (by decide)) (append (widen s20032_64 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide)))))))))))))

theorem claim782 : CheckedClaim verifiedRow ⟨2,1,2,20040,24016,-3073343609,10758486096⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 20040 3977 ⟨-3072806499,10757948986⟩
  rw [← get_eq_raw]
  exact (append (widen s20040_8 (by decide)) (append (widen s20048_16 (by decide)) (append (widen s20064_32 (by decide)) (append (widen s20096_128 (by decide)) (append (widen s20224_256 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))))

theorem claim783 : CheckedClaim verifiedRow ⟨2,1,2,21932,23920,-2214739371,9322906854⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 21932 1989 ⟨-2214202261,9322369744⟩
  rw [← get_eq_raw]
  exact (append (widen s21932_4 (by decide)) (append (widen s21936_16 (by decide)) (append (widen s21952_64 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))

theorem claim784 : CheckedClaim verifiedRow ⟨2,1,2,21964,23952,-2498215447,9233529443⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 21964 1989 ⟨-2497678337,9232992333⟩
  rw [← get_eq_raw]
  exact (append (widen s21964_4 (by decide)) (append (widen s21968_16 (by decide)) (append (widen s21984_32 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide))))))))))

theorem claim785 : CheckedClaim verifiedRow ⟨2,1,2,21996,23984,-2784427971,9141187513⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 21996 1989 ⟨-2783890861,9140650403⟩
  rw [← get_eq_raw]
  exact (append (widen s21996_4 (by decide)) (append (widen s22000_16 (by decide)) (append (widen s22016_512 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))

private theorem s24064_512 : Run get 24064 512 ⟨-8515176191,-3511172720⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨-14007593573,-8525507920⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨-19727501868,-14018635697⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨-19727501868,-8525507920⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

theorem claim786 : CheckedClaim verifiedRow ⟨2,1,2,23920,25908,-23162288748,-2213665145⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 23920 1989 ⟨-23161751638,-2214202255⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_32 (by decide)) (append (widen s25888_16 (by decide)) (append (widen s25904_4 (by decide)) (widen s25908_1 (by decide))))))))))

private theorem s25600_512 : Run get 25600 512 ⟨-25365762356,-19738702235⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨-30572619890,-25376470845⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨-30572619890,-19738702235⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨-30572619890,-8525507920⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨-34980943937,-30582127895⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨-38234353736,-34988535180⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨-38234353736,-30582127895⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

theorem claim787 : CheckedClaim verifiedRow ⟨2,1,2,23920,27896,-39302936831,-2213665145⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 23920 3977 ⟨-39302399721,-2214202255⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide))))))))))))

theorem claim788 : CheckedClaim verifiedRow ⟨2,1,2,23952,25940,-23513285589,-2497141221⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 23952 1989 ⟨-23512748479,-2497678331⟩
  rw [← get_eq_raw]
  exact (append (widen s23952_16 (by decide)) (append (widen s23968_32 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_16 (by decide)) (append (widen s25936_4 (by decide)) (widen s25940_1 (by decide)))))))))))

theorem claim789 : CheckedClaim verifiedRow ⟨2,1,2,23984,25972,-23863074668,-2783353745⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 23984 1989 ⟨-23862537558,-2783890855⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_1024 (by decide)) (append (widen s25600_256 (by decide)) (append (widen s25856_64 (by decide)) (append (widen s25920_32 (by decide)) (append (widen s25952_16 (by decide)) (append (widen s25968_4 (by decide)) (widen s25972_1 (by decide)))))))))))

theorem claim790 : CheckedClaim verifiedRow ⟨2,1,2,23984,27960,-39517280068,-2783353745⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 23984 3977 ⟨-39516742958,-2783890855⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim791 : CheckedClaim verifiedRow ⟨2,1,2,24016,27992,-39614892741,-3072269383⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 24016 3977 ⟨-39614355631,-3072806493⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_2048 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide)))))))))))

private theorem s27648_512 : Run get 27648 512 ⟨-40017872515,-38239362557⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨-40280428501,-40019744363⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨-40280428501,-38239362557⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨-40280428501,-30582127895⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨-40280428501,-8525507920⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨-40086513771,-38300137356⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨-38294788556,-34626758193⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨-40086513771,-34626758193⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

private theorem s29696_512 : Run get 29696 512 ⟨-34617783881,-29169510783⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨-29157236381,-22157712873⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨-34617783881,-22157712873⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨-40086513771,-22157712873⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨-22142705148,-13936144009⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨-13919175721,-4941697945⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨-22142705148,-4941697945⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim792 : CheckedClaim verifiedRow ⟨2,1,2,24016,31968,-40280965611,-870583302⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 24016 7953 ⟨-40280428501,-871120412⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim793 : CheckedClaim verifiedRow ⟨2,1,2,25908,27896,-39302936831,-23161214522⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 25908 1989 ⟨-39302399721,-23161751632⟩
  rw [← get_eq_raw]
  exact (append (widen s25908_4 (by decide)) (append (widen s25912_8 (by decide)) (append (widen s25920_64 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_128 (by decide)) (append (widen s27776_64 (by decide)) (append (widen s27840_32 (by decide)) (append (widen s27872_16 (by decide)) (append (widen s27888_8 (by decide)) (widen s27896_1 (by decide)))))))))))))

theorem claim794 : CheckedClaim verifiedRow ⟨2,1,2,25940,27928,-39413275258,-23512211363⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 25940 1989 ⟨-39412738148,-23512748473⟩
  rw [← get_eq_raw]
  exact (append (widen s25940_4 (by decide)) (append (widen s25944_8 (by decide)) (append (widen s25952_32 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_16 (by decide)) (append (widen s27920_8 (by decide)) (widen s27928_1 (by decide)))))))))))

theorem claim795 : CheckedClaim verifiedRow ⟨2,1,2,25972,27960,-39517280068,-23862000442⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 25972 1989 ⟨-39516742958,-23862537552⟩
  rw [← get_eq_raw]
  exact (append (widen s25972_4 (by decide)) (append (widen s25976_8 (by decide)) (append (widen s25984_128 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_32 (by decide)) (append (widen s27936_16 (by decide)) (append (widen s27952_8 (by decide)) (widen s27960_1 (by decide)))))))))))

theorem claim796 : CheckedClaim verifiedRow ⟨2,1,2,26004,27992,-39614892741,-24210494291⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 26004 1989 ⟨-39614355631,-24211031401⟩
  rw [← get_eq_raw]
  exact (append (widen s26004_4 (by decide)) (append (widen s26008_8 (by decide)) (append (widen s26016_32 (by decide)) (append (widen s26048_64 (by decide)) (append (widen s26112_512 (by decide)) (append (widen s26624_1024 (by decide)) (append (widen s27648_256 (by decide)) (append (widen s27904_64 (by decide)) (append (widen s27968_16 (by decide)) (append (widen s27984_8 (by decide)) (widen s27992_1 (by decide))))))))))))

theorem claim797 : CheckedClaim verifiedRow ⟨2,1,2,27896,31872,-40280965611,-2611099780⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 27896 3977 ⟨-40280428501,-2611636890⟩
  rw [← get_eq_raw]
  exact (append (widen s27896_8 (by decide)) (append (widen s27904_256 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (widen s31872_1 (by decide))))))))

theorem claim798 : CheckedClaim verifiedRow ⟨2,1,2,27960,29948,-40280965611,-32141159732⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 27960 1989 ⟨-40280428501,-32141696842⟩
  rw [← get_eq_raw]
  exact (append (widen s27960_8 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_128 (by decide)) (append (widen s29824_64 (by decide)) (append (widen s29888_32 (by decide)) (append (widen s29920_16 (by decide)) (append (widen s29936_8 (by decide)) (append (widen s29944_4 (by decide)) (widen s29948_1 (by decide)))))))))))))

theorem claim799 : CheckedClaim verifiedRow ⟨2,1,2,27960,31936,-40280965611,-1451117317⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 27960 3977 ⟨-40280428501,-1451654427⟩
  rw [← get_eq_raw]
  exact (append (widen s27960_8 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide))))))))))

theorem claim800 : CheckedClaim verifiedRow ⟨2,1,2,27992,29980,-40280965611,-31796798045⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 27992 1989 ⟨-40280428501,-31797335155⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_1024 (by decide)) (append (widen s29696_256 (by decide)) (append (widen s29952_16 (by decide)) (append (widen s29968_8 (by decide)) (append (widen s29976_4 (by decide)) (widen s29980_1 (by decide)))))))))))

theorem claim801 : CheckedClaim verifiedRow ⟨2,1,2,27992,31968,-40280965611,-870583302⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 27992 3977 ⟨-40280428501,-871120412⟩
  rw [← get_eq_raw]
  exact (append (widen s27992_8 (by decide)) (append (widen s28000_32 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim802 : CheckedClaim verifiedRow ⟨2,1,2,29948,31936,-32142233958,-1451117317⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 29948 1989 ⟨-32141696848,-1451654427⟩
  rw [← get_eq_raw]
  exact (append (widen s29948_4 (by decide)) (append (widen s29952_256 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide))))))))

theorem claim803 : CheckedClaim verifiedRow ⟨2,1,2,29980,31968,-31797872271,-870583302⟩ := by
  change Run (rawBlock verifiedRow 2 1 .second) 29980 1989 ⟨-31797335161,-871120412⟩
  rw [← get_eq_raw]
  exact (append (widen s29980_4 (by decide)) (append (widen s29984_32 (by decide)) (append (widen s30016_64 (by decide)) (append (widen s30080_128 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
