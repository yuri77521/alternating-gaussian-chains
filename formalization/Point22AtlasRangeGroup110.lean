import Point22AtlasRangeGroup110Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf110

private abbrev get := fastBlock verifiedRow 1 1 .value
private theorem get_eq_raw : get = rawBlock verifiedRow 1 1 .value :=
  funext (fastBlock_eq_raw verifiedRow 1 1 .value)

private theorem s512_512 : Run get 512 512 ⟨97776686150,99438383069⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

private theorem s1024_512 : Run get 1024 512 ⟨95063792555,97772386174⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

theorem claim0 : CheckedClaim verifiedRow ⟨1,1,0,32,2020,91606784987,99997800620⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 32 1989 ⟨91606785525,99997800082⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_512 (by decide)) (append (widen s1536_256 (by decide)) (append (widen s1792_128 (by decide)) (append (widen s1920_64 (by decide)) (append (widen s1984_32 (by decide)) (append (widen s2016_4 (by decide)) (widen s2020_1 (by decide)))))))))))))

private theorem s1536_512 : Run get 1536 512 ⟨91390923581,95057520597⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨91390923581,97772386174⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

private theorem s2048_512 : Run get 2048 512 ⟨86875857462,91382883500⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

private theorem s2560_512 : Run get 2560 512 ⟨81658848408,86866303514⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨81658848408,91382883500⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨75895409597,81648071911⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

theorem claim1 : CheckedClaim verifiedRow ⟨1,1,0,32,4008,70813090125,99997800620⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 32 3977 ⟨70813090663,99997800082⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_1024 (by decide)) (append (widen s3072_512 (by decide)) (append (widen s3584_256 (by decide)) (append (widen s3840_128 (by decide)) (append (widen s3968_32 (by decide)) (append (widen s4000_8 (by decide)) (widen s4008_1 (by decide))))))))))))))

private theorem s3584_512 : Run get 3584 512 ⟨69748662317,75883724241⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨69748662317,81648071911⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

private theorem s2048_2048 : Run get 2048 2048 ⟨69748662317,91382883500⟩ :=
  join s2048_1024 s3072_1024 (by decide) (by decide)

private theorem s4096_512 : Run get 4096 512 ⟨63381772603,69736389141⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

private theorem s4608_512 : Run get 4608 512 ⟨56950956343,63369225633⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨56950956343,69736389141⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨50599455092,56938429762⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

private theorem s5632_512 : Run get 5632 512 ⟨44452778310,50587212640⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨44452778310,56938429762⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨44452778310,69736389141⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨38615385774,44441045363⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨33168859780,38604344325⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨33168859780,44441045363⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨28171502184,33158646302⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim2 : CheckedClaim verifiedRow ⟨1,1,0,32,7984,25423679485,99997800620⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 32 7953 ⟨25423680023,99997800082⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_32 (by decide)) (append (widen s7968_16 (by decide)) (widen s7984_1 (by decide)))))))))))))))

private theorem s7680_512 : Run get 7680 512 ⟨23659196130,28162208146⟩ :=
  join s7680_256 s7936_256 (by decide) (by decide)

private theorem s7168_1024 : Run get 7168 1024 ⟨23659196130,33158646302⟩ :=
  join s7168_512 s7680_512 (by decide) (by decide)

private theorem s6144_2048 : Run get 6144 2048 ⟨23659196130,44441045363⟩ :=
  join s6144_1024 s7168_1024 (by decide) (by decide)

private theorem s4096_4096 : Run get 4096 4096 ⟨23659196130,69736389141⟩ :=
  join s4096_2048 s6144_2048 (by decide) (by decide)

private theorem s8192_512 : Run get 8192 512 ⟨19647302925,23650870777⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

private theorem s8704_512 : Run get 8704 512 ⟨16133323865,19639957819⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨16133323865,23650870777⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨13100044684,16126938653⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

private theorem s9728_512 : Run get 9728 512 ⟨10518893293,13094573527⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨10518893293,16126938653⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨10518893293,23650870777⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨8353274529,10514271475⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨6561692217,8349424813⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨6561692217,10514271475⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨5100522469,6558530638⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

private theorem s11776_512 : Run get 11776 512 ⟨3926356577,5097963345⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨3926356577,6558530638⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨3926356577,10514271475⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨3926356577,23650870777⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨2997882132,3924316641⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨2277313422,2996283751⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨2277313422,3924316641⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨1731414501,2276086974⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

private theorem s13824_512 : Run get 13824 512 ⟨1332179733,1730500018⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨1332179733,2276086974⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨1332179733,3924316641⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨1057247286,1331527940⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨890122077,1056820199⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨890122077,1331527940⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨820277513,889893299⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim3 : CheckedClaim verifiedRow ⟨1,1,0,32,15936,818073081,99997800620⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 32 15905 ⟨818073619,99997800082⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide)))))))))))))))

private theorem s15872_512 : Run get 15872 512 ⟨817354286,843191858⟩ :=
  join s15872_256 s16128_256 (by decide) (by decide)

private theorem s15360_1024 : Run get 15360 1024 ⟨817354286,889893299⟩ :=
  join s15360_512 s15872_512 (by decide) (by decide)

private theorem s14336_2048 : Run get 14336 2048 ⟨817354286,1331527940⟩ :=
  join s14336_1024 s15360_1024 (by decide) (by decide)

private theorem s12288_4096 : Run get 12288 4096 ⟨817354286,3924316641⟩ :=
  join s12288_2048 s14336_2048 (by decide) (by decide)

private theorem s8192_8192 : Run get 8192 8192 ⟨817354286,23650870777⟩ :=
  join s8192_4096 s12288_4096 (by decide) (by decide)

private theorem s16384_512 : Run get 16384 512 ⟨843327366,960356864⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨960681841,1179275405⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨843327366,1179275405⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨1179810379,1513442511⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

private theorem s17920_512 : Run get 17920 512 ⟨1514219674,1982282502⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨1179810379,1982282502⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨843327366,1982282502⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨1983345513,2610995065⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨2612398624,3430247066⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨1983345513,3430247066⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

private theorem s19456_512 : Run get 19456 512 ⟨3432056113,4475636279⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

private theorem s19968_512 : Run get 19968 512 ⟨4477924673,5786849933⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨3432056113,5786849933⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨1983345513,5786849933⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨843327366,5786849933⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨5789698463,7406446592⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨7409940185,9378205812⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨5789698463,9378205812⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

private theorem s21504_512 : Run get 21504 512 ⟨9382429868,11745016902⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨11750052714,14546315597⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨9382429868,14546315597⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨5789698463,14546315597⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨14552234932,17815124191⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨17821983181,21574803517⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨14552234932,21574803517⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

private theorem s23552_512 : Run get 23552 512 ⟨21582636135,25835679948⟩ :=
  join s23552_256 s23808_256 (by decide) (by decide)

private theorem s24064_512 : Run get 24064 512 ⟨25844491425,30591761472⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s23552_1024 : Run get 23552 1024 ⟨21582636135,30591761472⟩ :=
  join s23552_512 s24064_512 (by decide) (by decide)

private theorem s22528_2048 : Run get 22528 2048 ⟨14552234932,30591761472⟩ :=
  join s22528_1024 s23552_1024 (by decide) (by decide)

private theorem s20480_4096 : Run get 20480 4096 ⟨5789698463,30591761472⟩ :=
  join s20480_2048 s22528_2048 (by decide) (by decide)

private theorem s16384_8192 : Run get 16384 8192 ⟨843327366,30591761472⟩ :=
  join s16384_4096 s20480_4096 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨30601522137,35817797662⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨35828437710,41466962161⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨30601522137,41466962161⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

private theorem s25600_512 : Run get 25600 512 ⟨41478367926,47469437415⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨47481449659,53732155322⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨41478367926,53732155322⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨30601522137,53732155322⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨53744570001,60139892421⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨60152464243,66557835432⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨53744570001,66557835432⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

private theorem s27648_512 : Run get 27648 512 ⟨66570284328,72835627147⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨72847647573,78812781986⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨66570284328,78812781986⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨53744570001,78812781986⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨30601522137,78812781986⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨78824054707,84325235857⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨84335441635,89212679038⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨78824054707,89212679038⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

private theorem s29696_512 : Run get 29696 512 ⟨89221513444,93326226581⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨93333414979,96535919916⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨89221513444,96535919916⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨78824054707,96535919916⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨96541231608,98737534749⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨98740795259,99858198546⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨96541231608,99858198546⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim4 : CheckedClaim verifiedRow ⟨1,1,0,32,31840,817353748,99997800620⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 32 31809 ⟨817354286,99997800082⟩
  rw [← get_eq_raw]
  exact (append (widen s32_32 (by decide)) (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_64 (by decide)) (append (widen s31808_32 (by decide)) (widen s31840_1 (by decide)))))))))))))))))

theorem claim5 : CheckedClaim verifiedRow ⟨1,1,0,64,2052,91350690445,99991200983⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 64 1989 ⟨91350690983,99991200445⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide))))))))

theorem claim6 : CheckedClaim verifiedRow ⟨1,1,0,96,16000,817353748,99980202556⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 96 15905 ⟨817354286,99980202018⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))))))))

theorem claim7 : CheckedClaim verifiedRow ⟨1,1,0,96,31904,817353748,99980202556⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 96 31809 ⟨817354286,99980202018⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide))))))))))))))))

theorem claim8 : CheckedClaim verifiedRow ⟨1,1,0,7984,15936,818073081,25423680564⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 7984 7953 ⟨818073619,25423680026⟩
  rw [← get_eq_raw]
  exact (append (widen s7984_16 (by decide)) (append (widen s8000_64 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (widen s15936_1 (by decide))))))))))

theorem claim9 : CheckedClaim verifiedRow ⟨1,1,0,8016,15968,817533570,25145571072⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 8016 7953 ⟨817534108,25145570534⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))

theorem claim10 : CheckedClaim verifiedRow ⟨1,1,0,27864,31840,69244788470,99945015719⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 27864 3977 ⟨69244789008,99945015181⟩
  rw [← get_eq_raw]
  exact (append (widen s27864_8 (by decide)) (append (widen s27872_32 (by decide)) (append (widen s27904_256 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_64 (by decide)) (append (widen s31808_32 (by decide)) (widen s31840_1 (by decide))))))))))

theorem claim11 : CheckedClaim verifiedRow ⟨1,1,0,27896,31872,69638173164,99964806791⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 27896 3977 ⟨69638173702,99964806253⟩
  rw [← get_eq_raw]
  exact (append (widen s27896_8 (by decide)) (append (widen s27904_256 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (widen s31872_1 (by decide))))))))

theorem claim12 : CheckedClaim verifiedRow ⟨1,1,0,27928,31904,70030711297,99980202556⟩ := by
  change Run (rawBlock verifiedRow 1 1 .value) 27928 3977 ⟨70030711835,99980202018⟩
  rw [← get_eq_raw]
  exact (append (widen s27928_8 (by decide)) (append (widen s27936_32 (by decide)) (append (widen s27968_64 (by decide)) (append (widen s28032_128 (by decide)) (append (widen s28160_512 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
