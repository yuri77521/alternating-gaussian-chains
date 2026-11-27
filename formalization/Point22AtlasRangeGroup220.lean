import Point22AtlasRangeGroup220Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf220

private abbrev get := fastBlock verifiedRow 2 2 .value
private theorem get_eq_raw : get = rawBlock verifiedRow 2 2 .value :=
  funext (fastBlock_eq_raw verifiedRow 2 2 .value)

private theorem s512_512 : Run get 512 512 ⟨4108665,4325963⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

private theorem s1024_512 : Run get 1024 512 ⟨3759279,4108118⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

private theorem s1536_512 : Run get 1536 512 ⟨3297157,3758491⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨3297157,4108118⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

private theorem s2048_512 : Run get 2048 512 ⟨2746924,3296170⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

private theorem s2560_512 : Run get 2560 512 ⟨2136948,2745794⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨2136948,3296170⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨1497281,2135730⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

private theorem s3584_512 : Run get 3584 512 ⟨857630,1496034⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨857630,2135730⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

private theorem s2048_2048 : Run get 2048 2048 ⟨857630,3296170⟩ :=
  join s2048_1024 s3072_1024 (by decide) (by decide)

private theorem s4096_512 : Run get 4096 512 ⟨245444,856410⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

private theorem s4608_512 : Run get 4608 512 ⟨-315643,244304⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨-315643,856410⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨-806993,-316663⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

private theorem s5632_512 : Run get 5632 512 ⟨-1215628,-807863⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨-1215628,-316663⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨-1215628,856410⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨-1534432,-1216328⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨-1761885,-1534953⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨-1761885,-1216328⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨-1901425,-1762229⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim804 : CheckedClaim verifiedRow ⟨2,2,0,64,8016,-1950937,4400945⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 64 7953 ⟨-1948788,4398796⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide))))))))))))))

private theorem s7680_512 : Run get 7680 512 ⟨-1960556,-1901605⟩ :=
  join s7680_256 s7936_256 (by decide) (by decide)

private theorem s7168_1024 : Run get 7168 1024 ⟨-1960556,-1762229⟩ :=
  join s7168_512 s7680_512 (by decide) (by decide)

private theorem s6144_2048 : Run get 6144 2048 ⟨-1960556,-1216328⟩ :=
  join s6144_1024 s7168_1024 (by decide) (by decide)

private theorem s4096_4096 : Run get 4096 4096 ⟨-1960556,856410⟩ :=
  join s4096_2048 s6144_2048 (by decide) (by decide)

private theorem s8192_512 : Run get 8192 512 ⟨-1964146,-1949752⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

private theorem s8704_512 : Run get 8704 512 ⟨-1949683,-1881410⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨-1964146,-1881410⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨-1881240,-1768709⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

private theorem s9728_512 : Run get 9728 512 ⟨-1768467,-1624742⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨-1881240,-1624742⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨-1964146,-1624742⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨-1624451,-1461746⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨-1461429,-1290578⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨-1624451,-1290578⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨-1290253,-1120402⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

private theorem s11776_512 : Run get 11776 512 ⟨-1120090,-958564⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨-1290253,-958564⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨-1624451,-958564⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨-1964146,-958564⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨-958273,-810635⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨-810375,-680590⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨-958273,-680590⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨-680369,-571063⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

private theorem s13824_512 : Run get 13824 512 ⟨-570882,-483642⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨-680369,-483642⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨-958273,-483642⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨-483506,-419179⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨-419087,-378048⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨-483506,-378048⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨-378003,-360384⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim805 : CheckedClaim verifiedRow ⟨2,2,0,64,15968,-1966295,4400945⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 64 15905 ⟨-1964146,4398796⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))))))

private theorem s15872_512 : Run get 15872 512 ⟨-366224,-359637⟩ :=
  join s15872_256 s16128_256 (by decide) (by decide)

private theorem s15360_1024 : Run get 15360 1024 ⟨-378003,-359637⟩ :=
  join s15360_512 s15872_512 (by decide) (by decide)

private theorem s14336_2048 : Run get 14336 2048 ⟨-483506,-359637⟩ :=
  join s14336_1024 s15360_1024 (by decide) (by decide)

private theorem s12288_4096 : Run get 12288 4096 ⟨-958273,-359637⟩ :=
  join s12288_2048 s14336_2048 (by decide) (by decide)

private theorem s8192_8192 : Run get 8192 8192 ⟨-1964146,-359637⟩ :=
  join s8192_4096 s12288_4096 (by decide) (by decide)

private theorem s16384_512 : Run get 16384 512 ⟨-395536,-366246⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨-448269,-395604⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨-448269,-366246⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨-524194,-448384⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

private theorem s17920_512 : Run get 17920 512 ⟨-622726,-524351⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨-622726,-448384⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨-622726,-366246⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨-742689,-622927⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨-882011,-742931⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨-882011,-622927⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

private theorem s19456_512 : Run get 19456 512 ⟨-1037432,-882288⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

private theorem s19968_512 : Run get 19968 512 ⟨-1204212,-1037738⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨-1204212,-882288⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨-1204212,-622927⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨-1204212,-366246⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨-1375909,-1204532⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨-1544280,-1376233⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨-1544280,-1204532⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

private theorem s21504_512 : Run get 21504 512 ⟨-1699290,-1544588⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨-1829344,-1699559⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨-1829344,-1544588⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨-1829344,-1204532⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨-1921699,-1829552⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨-1963113,-1921822⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨-1963113,-1829552⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

private theorem s23552_512 : Run get 23552 512 ⟨-1964146,-1940660⟩ :=
  join s23552_256 s23808_256 (by decide) (by decide)

private theorem s24064_512 : Run get 24064 512 ⟨-1940559,-1842789⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s23552_1024 : Run get 23552 1024 ⟨-1964146,-1842789⟩ :=
  join s23552_512 s24064_512 (by decide) (by decide)

private theorem s22528_2048 : Run get 22528 2048 ⟨-1964146,-1829552⟩ :=
  join s22528_1024 s23552_1024 (by decide) (by decide)

private theorem s20480_4096 : Run get 20480 4096 ⟨-1964146,-1204532⟩ :=
  join s20480_2048 s22528_2048 (by decide) (by decide)

private theorem s16384_8192 : Run get 16384 8192 ⟨-1964146,-366246⟩ :=
  join s16384_4096 s20480_4096 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨-1842529,-1660345⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨-1659913,-1387712⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨-1842529,-1387712⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

private theorem s25600_512 : Run get 25600 512 ⟨-1387103,-1023814⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨-1023029,-572891⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨-1387103,-572891⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨-1842529,-572891⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨-571945,-44961⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨-43876,544138⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨-571945,544138⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

private theorem s27648_512 : Run get 27648 512 ⟨545323,1173174⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨1174413,1816446⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨545323,1816446⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨-571945,1816446⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨-1842529,1816446⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨1817686,2445165⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨2446347,3029203⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨1817686,3029203⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

private theorem s29696_512 : Run get 29696 512 ⟨3030269,3539083⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨3539977,3948049⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨3030269,3948049⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨1817686,3948049⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨3948721,4234020⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨4234434,4381249⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨3948721,4381249⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim806 : CheckedClaim verifiedRow ⟨2,2,0,64,31872,-1966295,4400945⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 64 31809 ⟨-1964146,4398796⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (widen s31872_1 (by decide)))))))))))))))

theorem claim807 : CheckedClaim verifiedRow ⟨2,2,0,96,16000,-1966295,4399493⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 96 15905 ⟨-1964146,4397344⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))))))))

theorem claim808 : CheckedClaim verifiedRow ⟨2,2,0,128,31936,-1966295,4400945⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 128 31809 ⟨-1964146,4398796⟩
  rw [← get_eq_raw]
  exact (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide)))))))))))))))

theorem claim809 : CheckedClaim verifiedRow ⟨2,2,0,8016,15968,-1966295,-357534⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 8016 7953 ⟨-1964146,-359683⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))

theorem claim810 : CheckedClaim verifiedRow ⟨2,2,0,15968,23920,-1966295,-357488⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 15968 7953 ⟨-1964146,-359637⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide))))))))))))

theorem claim811 : CheckedClaim verifiedRow ⟨2,2,0,16000,31904,-1966295,4399493⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 16000 15905 ⟨-1964146,4397344⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide))))))))))

theorem claim812 : CheckedClaim verifiedRow ⟨2,2,0,23920,31872,-1956218,4397462⟩ := by
  change Run (rawBlock verifiedRow 2 2 .value) 23920 7953 ⟨-1954069,4395313⟩
  rw [← get_eq_raw]
  exact (append (widen s23920_16 (by decide)) (append (widen s23936_128 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (widen s31872_1 (by decide)))))))))

end GaussianChains.Point22.Atlas.RangeTicks
