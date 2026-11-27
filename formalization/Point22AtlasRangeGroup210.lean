import Point22AtlasRangeGroup210Part7

/-! Verified signed-kernel range facts generated from the frozen atlas. -/
namespace GaussianChains.Point22.Atlas.RangeTicks
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

open Leaf210

private abbrev get := fastBlock verifiedRow 2 1 .value
private theorem get_eq_raw : get = rawBlock verifiedRow 2 1 .value :=
  funext (fastBlock_eq_raw verifiedRow 2 1 .value)

private theorem s512_512 : Run get 512 512 ⟨-135477814,-67840104⟩ :=
  join s512_256 s768_256 (by decide) (by decide)

private theorem s1024_512 : Run get 1024 512 ⟨-198760103,-135606473⟩ :=
  join s1024_256 s1280_256 (by decide) (by decide)

private theorem s1536_512 : Run get 1536 512 ⟨-255577262,-198877961⟩ :=
  join s1536_256 s1792_256 (by decide) (by decide)

private theorem s1024_1024 : Run get 1024 1024 ⟨-255577262,-135606473⟩ :=
  join s1024_512 s1536_512 (by decide) (by decide)

theorem claim613 : CheckedClaim verifiedRow ⟨2,1,0,64,2052,-256095620,-6598559⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 64 1989 ⟨-256094545,-6599634⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_4 (by decide)) (widen s2052_1 (by decide))))))))

private theorem s2048_512 : Run get 2048 512 ⟨-304303972,-255680775⟩ :=
  join s2048_256 s2304_256 (by decide) (by decide)

private theorem s2560_512 : Run get 2560 512 ⟨-343739591,-304390360⟩ :=
  join s2560_256 s2816_256 (by decide) (by decide)

private theorem s2048_1024 : Run get 2048 1024 ⟨-343739591,-255680775⟩ :=
  join s2048_512 s2560_512 (by decide) (by decide)

private theorem s3072_512 : Run get 3072 512 ⟨-373152740,-343806961⟩ :=
  join s3072_256 s3328_256 (by decide) (by decide)

private theorem s3584_512 : Run get 3584 512 ⟨-392292943,-373200134⟩ :=
  join s3584_256 s3840_256 (by decide) (by decide)

private theorem s3072_1024 : Run get 3072 1024 ⟨-392292943,-343806961⟩ :=
  join s3072_512 s3584_512 (by decide) (by decide)

private theorem s2048_2048 : Run get 2048 2048 ⟨-392292943,-255680775⟩ :=
  join s2048_1024 s3072_1024 (by decide) (by decide)

private theorem s4096_512 : Run get 4096 512 ⟨-401370453,-392320335⟩ :=
  join s4096_256 s4352_256 (by decide) (by decide)

private theorem s4608_512 : Run get 4608 512 ⟨-402324972,-401007935⟩ :=
  join s4608_256 s4864_256 (by decide) (by decide)

private theorem s4096_1024 : Run get 4096 1024 ⟨-402324972,-392320335⟩ :=
  join s4096_512 s4608_512 (by decide) (by decide)

private theorem s5120_512 : Run get 5120 512 ⟨-400998578,-392169960⟩ :=
  join s5120_256 s5376_256 (by decide) (by decide)

private theorem s5632_512 : Run get 5632 512 ⟨-392145176,-376077418⟩ :=
  join s5632_256 s5888_256 (by decide) (by decide)

private theorem s5120_1024 : Run get 5120 1024 ⟨-400998578,-376077418⟩ :=
  join s5120_512 s5632_512 (by decide) (by decide)

private theorem s4096_2048 : Run get 4096 2048 ⟨-402324972,-376077418⟩ :=
  join s4096_1024 s5120_1024 (by decide) (by decide)

private theorem s6144_512 : Run get 6144 512 ⟨-376039782,-354114817⟩ :=
  join s6144_256 s6400_256 (by decide) (by decide)

private theorem s6656_512 : Run get 6656 512 ⟨-354067131,-327737956⟩ :=
  join s6656_256 s6912_256 (by decide) (by decide)

private theorem s6144_1024 : Run get 6144 1024 ⟨-376039782,-327737956⟩ :=
  join s6144_512 s6656_512 (by decide) (by decide)

private theorem s7168_512 : Run get 7168 512 ⟨-327683077,-298388700⟩ :=
  join s7168_256 s7424_256 (by decide) (by decide)

theorem claim614 : CheckedClaim verifiedRow ⟨2,1,0,64,8016,-402326047,-6598559⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 64 7953 ⟨-402324972,-6599634⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_16 (by decide)) (widen s8016_1 (by decide))))))))))))))

private theorem s7680_512 : Run get 7680 512 ⟨-298329381,-267422086⟩ :=
  join s7680_256 s7936_256 (by decide) (by decide)

private theorem s7168_1024 : Run get 7168 1024 ⟨-327683077,-267422086⟩ :=
  join s7168_512 s7680_512 (by decide) (by decide)

private theorem s6144_2048 : Run get 6144 2048 ⟨-376039782,-267422086⟩ :=
  join s6144_1024 s7168_1024 (by decide) (by decide)

private theorem s4096_4096 : Run get 4096 4096 ⟨-402324972,-267422086⟩ :=
  join s4096_2048 s6144_2048 (by decide) (by decide)

private theorem s8192_512 : Run get 8192 512 ⟨-267360846,-236049260⟩ :=
  join s8192_256 s8448_256 (by decide) (by decide)

private theorem s8704_512 : Run get 8704 512 ⟨-235988297,-205297953⟩ :=
  join s8704_256 s8960_256 (by decide) (by decide)

private theorem s8192_1024 : Run get 8192 1024 ⟨-267360846,-205297953⟩ :=
  join s8192_512 s8704_512 (by decide) (by decide)

private theorem s9216_512 : Run get 9216 512 ⟨-205239077,-175990457⟩ :=
  join s9216_256 s9472_256 (by decide) (by decide)

private theorem s9728_512 : Run get 9728 512 ⟨-175935068,-148737642⟩ :=
  join s9728_256 s9984_256 (by decide) (by decide)

private theorem s9216_1024 : Run get 9216 1024 ⟨-205239077,-148737642⟩ :=
  join s9216_512 s9728_512 (by decide) (by decide)

private theorem s8192_2048 : Run get 8192 2048 ⟨-267360846,-148737642⟩ :=
  join s8192_1024 s9216_1024 (by decide) (by decide)

private theorem s10240_512 : Run get 10240 512 ⟨-148686728,-123946477⟩ :=
  join s10240_256 s10496_256 (by decide) (by decide)

private theorem s10752_512 : Run get 10752 512 ⟨-123900644,-101837885⟩ :=
  join s10752_256 s11008_256 (by decide) (by decide)

private theorem s10240_1024 : Run get 10240 1024 ⟨-148686728,-101837885⟩ :=
  join s10240_512 s10752_512 (by decide) (by decide)

private theorem s11264_512 : Run get 11264 512 ⟨-101797397,-82471488⟩ :=
  join s11264_256 s11520_256 (by decide) (by decide)

private theorem s11776_512 : Run get 11776 512 ⟨-82436324,-65773914⟩ :=
  join s11776_256 s12032_256 (by decide) (by decide)

private theorem s11264_1024 : Run get 11264 1024 ⟨-101797397,-65773914⟩ :=
  join s11264_512 s11776_512 (by decide) (by decide)

private theorem s10240_2048 : Run get 10240 2048 ⟨-148686728,-65773914⟩ :=
  join s10240_1024 s11264_1024 (by decide) (by decide)

private theorem s8192_4096 : Run get 8192 4096 ⟨-267360846,-65773914⟩ :=
  join s8192_2048 s10240_2048 (by decide) (by decide)

private theorem s12288_512 : Run get 12288 512 ⟨-65743818,-51567723⟩ :=
  join s12288_256 s12544_256 (by decide) (by decide)

private theorem s12800_512 : Run get 12800 512 ⟨-51542264,-39598588⟩ :=
  join s12800_256 s13056_256 (by decide) (by decide)

private theorem s12288_1024 : Run get 12288 1024 ⟨-65743818,-39598588⟩ :=
  join s12288_512 s12800_512 (by decide) (by decide)

private theorem s13312_512 : Run get 13312 512 ⟨-39577213,-29559027⟩ :=
  join s13312_256 s13568_256 (by decide) (by decide)

private theorem s13824_512 : Run get 13824 512 ⟨-29541093,-21107649⟩ :=
  join s13824_256 s14080_256 (by decide) (by decide)

private theorem s13312_1024 : Run get 13312 1024 ⟨-39577213,-21107649⟩ :=
  join s13312_512 s13824_512 (by decide) (by decide)

private theorem s12288_2048 : Run get 12288 2048 ⟨-65743818,-21107649⟩ :=
  join s12288_1024 s13312_1024 (by decide) (by decide)

private theorem s14336_512 : Run get 14336 512 ⟨-21092469,-13883581⟩ :=
  join s14336_256 s14592_256 (by decide) (by decide)

private theorem s14848_512 : Run get 14848 512 ⟨-13870437,-7516224⟩ :=
  join s14848_256 s15104_256 (by decide) (by decide)

private theorem s14336_1024 : Run get 14336 1024 ⟨-21092469,-7516224⟩ :=
  join s14336_512 s14848_512 (by decide) (by decide)

private theorem s15360_512 : Run get 15360 512 ⟨-7504388,-1631038⟩ :=
  join s15360_256 s15616_256 (by decide) (by decide)

theorem claim615 : CheckedClaim verifiedRow ⟨2,1,0,64,15968,-402326047,-538433⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 64 15905 ⟨-402324972,-539508⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_64 (by decide)) (append (widen s15936_32 (by decide)) (widen s15968_1 (by decide)))))))))))))))

private theorem s15872_512 : Run get 15872 512 ⟨-1619776,4147695⟩ :=
  join s15872_256 s16128_256 (by decide) (by decide)

private theorem s15360_1024 : Run get 15360 1024 ⟨-7504388,4147695⟩ :=
  join s15360_512 s15872_512 (by decide) (by decide)

private theorem s14336_2048 : Run get 14336 2048 ⟨-21092469,4147695⟩ :=
  join s14336_1024 s15360_1024 (by decide) (by decide)

private theorem s12288_4096 : Run get 12288 4096 ⟨-65743818,4147695⟩ :=
  join s12288_2048 s14336_2048 (by decide) (by decide)

private theorem s8192_8192 : Run get 8192 8192 ⟨-267360846,4147695⟩ :=
  join s8192_4096 s12288_4096 (by decide) (by decide)

private theorem s16384_512 : Run get 16384 512 ⟨4159117,10195844⟩ :=
  join s16384_256 s16640_256 (by decide) (by decide)

private theorem s16896_512 : Run get 16896 512 ⟨10208160,16888813⟩ :=
  join s16896_256 s17152_256 (by decide) (by decide)

private theorem s16384_1024 : Run get 16384 1024 ⟨4159117,16888813⟩ :=
  join s16384_512 s16896_512 (by decide) (by decide)

private theorem s17408_512 : Run get 17408 512 ⟨16902754,24599924⟩ :=
  join s17408_256 s17664_256 (by decide) (by decide)

private theorem s17920_512 : Run get 17920 512 ⟨24616217,33696484⟩ :=
  join s17920_256 s18176_256 (by decide) (by decide)

private theorem s17408_1024 : Run get 17408 1024 ⟨16902754,33696484⟩ :=
  join s17408_512 s17920_512 (by decide) (by decide)

private theorem s16384_2048 : Run get 16384 2048 ⟨4159117,33696484⟩ :=
  join s16384_1024 s17408_1024 (by decide) (by decide)

private theorem s18432_512 : Run get 18432 512 ⟨33715835,44532380⟩ :=
  join s18432_256 s18688_256 (by decide) (by decide)

private theorem s18944_512 : Run get 18944 512 ⟨44555460,57436355⟩ :=
  join s18944_256 s19200_256 (by decide) (by decide)

private theorem s18432_1024 : Run get 18432 1024 ⟨33715835,57436355⟩ :=
  join s18432_512 s18944_512 (by decide) (by decide)

private theorem s19456_512 : Run get 19456 512 ⟨57463772,72695486⟩ :=
  join s19456_256 s19712_256 (by decide) (by decide)

private theorem s19968_512 : Run get 19968 512 ⟨72727745,90533907⟩ :=
  join s19968_256 s20224_256 (by decide) (by decide)

private theorem s19456_1024 : Run get 19456 1024 ⟨57463772,90533907⟩ :=
  join s19456_512 s19968_512 (by decide) (by decide)

private theorem s18432_2048 : Run get 18432 2048 ⟨33715835,90533907⟩ :=
  join s18432_1024 s19456_1024 (by decide) (by decide)

private theorem s16384_4096 : Run get 16384 4096 ⟨4159117,90533907⟩ :=
  join s16384_2048 s18432_2048 (by decide) (by decide)

private theorem s20480_512 : Run get 20480 512 ⟨90571372,111087427⟩ :=
  join s20480_256 s20736_256 (by decide) (by decide)

private theorem s20992_512 : Run get 20992 512 ⟨111130255,134375326⟩ :=
  join s20992_256 s21248_256 (by decide) (by decide)

private theorem s20480_1024 : Run get 20480 1024 ⟨90571372,134375326⟩ :=
  join s20480_512 s20992_512 (by decide) (by decide)

private theorem s21504_512 : Run get 21504 512 ⟨134423423,160271385⟩ :=
  join s21504_256 s21760_256 (by decide) (by decide)

private theorem s22016_512 : Run get 22016 512 ⟨160324345,188476724⟩ :=
  join s22016_256 s22272_256 (by decide) (by decide)

private theorem s21504_1024 : Run get 21504 1024 ⟨134423423,188476724⟩ :=
  join s21504_512 s22016_512 (by decide) (by decide)

private theorem s20480_2048 : Run get 20480 2048 ⟨90571372,188476724⟩ :=
  join s20480_1024 s21504_1024 (by decide) (by decide)

private theorem s22528_512 : Run get 22528 512 ⟨188533778,218497629⟩ :=
  join s22528_256 s22784_256 (by decide) (by decide)

private theorem s23040_512 : Run get 23040 512 ⟨218557610,249631758⟩ :=
  join s23040_256 s23296_256 (by decide) (by decide)

private theorem s22528_1024 : Run get 22528 1024 ⟨188533778,249631758⟩ :=
  join s22528_512 s23040_512 (by decide) (by decide)

private theorem s23552_512 : Run get 23552 512 ⟨249693088,280966115⟩ :=
  join s23552_256 s23808_256 (by decide) (by decide)

private theorem s24064_512 : Run get 24064 512 ⟨281026809,311389727⟩ :=
  join s24064_256 s24320_256 (by decide) (by decide)

private theorem s23552_1024 : Run get 23552 1024 ⟨249693088,311389727⟩ :=
  join s23552_512 s24064_512 (by decide) (by decide)

private theorem s22528_2048 : Run get 22528 2048 ⟨188533778,311389727⟩ :=
  join s22528_1024 s23552_1024 (by decide) (by decide)

private theorem s20480_4096 : Run get 20480 4096 ⟨90571372,311389727⟩ :=
  join s20480_2048 s22528_2048 (by decide) (by decide)

private theorem s16384_8192 : Run get 16384 8192 ⟨4159117,311389727⟩ :=
  join s16384_4096 s20480_4096 (by decide) (by decide)

private theorem s24576_512 : Run get 24576 512 ⟨311447439,339623157⟩ :=
  join s24576_256 s24832_256 (by decide) (by decide)

private theorem s25088_512 : Run get 25088 512 ⟨339675251,364265729⟩ :=
  join s25088_256 s25344_256 (by decide) (by decide)

private theorem s24576_1024 : Run get 24576 1024 ⟨311447439,364265729⟩ :=
  join s24576_512 s25088_512 (by decide) (by decide)

private theorem s25600_512 : Run get 25600 512 ⟨364309389,383859758⟩ :=
  join s25600_256 s25856_256 (by decide) (by decide)

private theorem s26112_512 : Run get 26112 512 ⟨383892132,396969336⟩ :=
  join s26112_256 s26368_256 (by decide) (by decide)

private theorem s25600_1024 : Run get 25600 1024 ⟨364309389,396969336⟩ :=
  join s25600_512 s26112_512 (by decide) (by decide)

private theorem s24576_2048 : Run get 24576 2048 ⟨311447439,396969336⟩ :=
  join s24576_1024 s25600_1024 (by decide) (by decide)

private theorem s26624_512 : Run get 26624 512 ⟨396987696,402269369⟩ :=
  join s26624_256 s26880_256 (by decide) (by decide)

private theorem s27136_512 : Run get 27136 512 ⟨398638957,402324972⟩ :=
  join s27136_256 s27392_256 (by decide) (by decide)

private theorem s26624_1024 : Run get 26624 1024 ⟨396987696,402324972⟩ :=
  join s26624_512 s27136_512 (by decide) (by decide)

private theorem s27648_512 : Run get 27648 512 ⟨385251991,398622538⟩ :=
  join s27648_256 s27904_256 (by decide) (by decide)

private theorem s28160_512 : Run get 28160 512 ⟨361657104,385215941⟩ :=
  join s28160_256 s28416_256 (by decide) (by decide)

private theorem s27648_1024 : Run get 27648 1024 ⟨361657104,398622538⟩ :=
  join s27648_512 s28160_512 (by decide) (by decide)

private theorem s26624_2048 : Run get 26624 2048 ⟨361657104,402324972⟩ :=
  join s26624_1024 s27648_1024 (by decide) (by decide)

private theorem s24576_4096 : Run get 24576 4096 ⟨311447439,402324972⟩ :=
  join s24576_2048 s26624_2048 (by decide) (by decide)

private theorem s28672_512 : Run get 28672 512 ⟨327839418,361600953⟩ :=
  join s28672_256 s28928_256 (by decide) (by decide)

private theorem s29184_512 : Run get 29184 512 ⟨284257257,327763592⟩ :=
  join s29184_256 s29440_256 (by decide) (by decide)

private theorem s28672_1024 : Run get 28672 1024 ⟨284257257,361600953⟩ :=
  join s28672_512 s29184_512 (by decide) (by decide)

private theorem s29696_512 : Run get 29696 512 ⟨231848839,284163124⟩ :=
  join s29696_256 s29952_256 (by decide) (by decide)

private theorem s30208_512 : Run get 30208 512 ⟨172006315,231738689⟩ :=
  join s30208_256 s30464_256 (by decide) (by decide)

private theorem s29696_1024 : Run get 29696 1024 ⟨172006315,284163124⟩ :=
  join s29696_512 s30208_512 (by decide) (by decide)

private theorem s28672_2048 : Run get 28672 2048 ⟨172006315,361600953⟩ :=
  join s28672_1024 s29696_1024 (by decide) (by decide)

private theorem s30720_512 : Run get 30720 512 ⟨106517324,171883277⟩ :=
  join s30720_256 s30976_256 (by decide) (by decide)

private theorem s31232_512 : Run get 31232 512 ⟨37477233,106385225⟩ :=
  join s31232_256 s31488_256 (by decide) (by decide)

private theorem s30720_1024 : Run get 30720 1024 ⟨37477233,171883277⟩ :=
  join s30720_512 s31232_512 (by decide) (by decide)

theorem claim616 : CheckedClaim verifiedRow ⟨2,1,0,64,31872,-402326047,402326047⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 64 31809 ⟨-402324972,402324972⟩
  rw [← get_eq_raw]
  exact (append (widen s64_64 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (widen s31872_1 (by decide)))))))))))))))

theorem claim617 : CheckedClaim verifiedRow ⟨2,1,0,96,8048,-402326047,-10997349⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 96 7953 ⟨-402324972,-10998424⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_64 (by decide)) (append (widen s8000_32 (by decide)) (append (widen s8032_16 (by decide)) (widen s8048_1 (by decide)))))))))))))))

theorem claim618 : CheckedClaim verifiedRow ⟨2,1,0,96,16000,-402326047,-178744⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 96 15905 ⟨-402324972,-179819⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (widen s16000_1 (by decide))))))))))))))

theorem claim619 : CheckedClaim verifiedRow ⟨2,1,0,96,23952,-402326047,274210221⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 96 23857 ⟨-402324972,274209146⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide))))))))))))))))

theorem claim620 : CheckedClaim verifiedRow ⟨2,1,0,96,31904,-402326047,402326047⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 96 31809 ⟨-402324972,402324972⟩
  rw [← get_eq_raw]
  exact (append (widen s96_32 (by decide)) (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide))))))))))))))))

theorem claim621 : CheckedClaim verifiedRow ⟨2,1,0,128,8080,-402326047,-15394687⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 128 7953 ⟨-402324972,-15395762⟩
  rw [← get_eq_raw]
  exact (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_16 (by decide)) (widen s8080_1 (by decide)))))))))))))

theorem claim622 : CheckedClaim verifiedRow ⟨2,1,0,128,16032,-402326047,180900⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 128 15905 ⟨-402324972,179825⟩
  rw [← get_eq_raw]
  exact (append (widen s128_128 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide))))))))))))))

theorem claim623 : CheckedClaim verifiedRow ⟨2,1,0,160,8112,-402326047,-19789994⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 160 7953 ⟨-402324972,-19791069⟩
  rw [← get_eq_raw]
  exact (append (widen s160_32 (by decide)) (append (widen s192_64 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_2048 (by decide)) (append (widen s6144_1024 (by decide)) (append (widen s7168_512 (by decide)) (append (widen s7680_256 (by decide)) (append (widen s7936_128 (by decide)) (append (widen s8064_32 (by decide)) (append (widen s8096_16 (by decide)) (widen s8112_1 (by decide)))))))))))))))

theorem claim624 : CheckedClaim verifiedRow ⟨2,1,0,160,16064,-402326047,540589⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 160 15905 ⟨-402324972,539514⟩
  rw [← get_eq_raw]
  exact (append (widen s160_32 (by decide)) (append (widen s192_64 (by decide)) (append (widen s256_256 (by decide)) (append (widen s512_512 (by decide)) (append (widen s1024_1024 (by decide)) (append (widen s2048_2048 (by decide)) (append (widen s4096_4096 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide)))))))))))))))

theorem claim625 : CheckedClaim verifiedRow ⟨2,1,0,8016,23920,-278110570,272256158⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 8016 15905 ⟨-278109495,272255083⟩
  rw [← get_eq_raw]
  exact (append (widen s8016_16 (by decide)) (append (widen s8032_32 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_64 (by decide)) (append (widen s23872_32 (by decide)) (append (widen s23904_16 (by decide)) (widen s23920_1 (by decide)))))))))))))

theorem claim626 : CheckedClaim verifiedRow ⟨2,1,0,8048,23952,-276161788,274210221⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 8048 15905 ⟨-276160713,274209146⟩
  rw [← get_eq_raw]
  exact (append (widen s8048_16 (by decide)) (append (widen s8064_128 (by decide)) (append (widen s8192_8192 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_16 (by decide)) (widen s23952_1 (by decide)))))))))))

theorem claim627 : CheckedClaim verifiedRow ⟨2,1,0,8080,16032,-274210221,180900⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 8080 7953 ⟨-274209146,179825⟩
  rw [← get_eq_raw]
  exact (append (widen s8080_16 (by decide)) (append (widen s8096_32 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_32 (by decide)) (widen s16032_1 (by decide)))))))))))

theorem claim628 : CheckedClaim verifiedRow ⟨2,1,0,8112,16064,-272256158,540589⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 8112 7953 ⟨-272255083,539514⟩
  rw [← get_eq_raw]
  exact (append (widen s8112_16 (by decide)) (append (widen s8128_64 (by decide)) (append (widen s8192_4096 (by decide)) (append (widen s12288_2048 (by decide)) (append (widen s14336_1024 (by decide)) (append (widen s15360_512 (by decide)) (append (widen s15872_128 (by decide)) (append (widen s16000_64 (by decide)) (widen s16064_1 (by decide))))))))))

theorem claim629 : CheckedClaim verifiedRow ⟨2,1,0,15968,31872,-540589,402326047⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 15968 15905 ⟨-539514,402324972⟩
  rw [← get_eq_raw]
  exact (append (widen s15968_32 (by decide)) (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (widen s31872_1 (by decide))))))))))

theorem claim630 : CheckedClaim verifiedRow ⟨2,1,0,16000,31904,-180900,402326047⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 16000 15905 ⟨-179825,402324972⟩
  rw [← get_eq_raw]
  exact (append (widen s16000_128 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide))))))))))

theorem claim631 : CheckedClaim verifiedRow ⟨2,1,0,16032,23984,178744,276161788⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 16032 7953 ⟨179819,276160713⟩
  rw [← get_eq_raw]
  exact (append (widen s16032_32 (by decide)) (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_32 (by decide)) (append (widen s23968_16 (by decide)) (widen s23984_1 (by decide))))))))))))

theorem claim632 : CheckedClaim verifiedRow ⟨2,1,0,16064,24016,538433,278110570⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 16064 7953 ⟨539508,278109495⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_4096 (by decide)) (append (widen s20480_2048 (by decide)) (append (widen s22528_1024 (by decide)) (append (widen s23552_256 (by decide)) (append (widen s23808_128 (by decide)) (append (widen s23936_64 (by decide)) (append (widen s24000_16 (by decide)) (widen s24016_1 (by decide)))))))))))

theorem claim633 : CheckedClaim verifiedRow ⟨2,1,0,16064,31968,538433,402326047⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 16064 15905 ⟨539508,402324972⟩
  rw [← get_eq_raw]
  exact (append (widen s16064_64 (by decide)) (append (widen s16128_256 (by decide)) (append (widen s16384_8192 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim634 : CheckedClaim verifiedRow ⟨2,1,0,23984,31936,10997349,402326047⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 23984 7953 ⟨10998424,402324972⟩
  rw [← get_eq_raw]
  exact (append (widen s23984_16 (by decide)) (append (widen s24000_64 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide))))))))))

theorem claim635 : CheckedClaim verifiedRow ⟨2,1,0,24016,31968,6598559,402326047⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 24016 7953 ⟨6599634,402324972⟩
  rw [← get_eq_raw]
  exact (append (widen s24016_16 (by decide)) (append (widen s24032_32 (by decide)) (append (widen s24064_512 (by decide)) (append (widen s24576_4096 (by decide)) (append (widen s28672_2048 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

theorem claim636 : CheckedClaim verifiedRow ⟨2,1,0,29916,31904,15394687,262647820⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 29916 1989 ⟨15395762,262646745⟩
  rw [← get_eq_raw]
  exact (append (widen s29916_4 (by decide)) (append (widen s29920_32 (by decide)) (append (widen s29952_256 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_32 (by decide)) (widen s31904_1 (by decide)))))))))

theorem claim637 : CheckedClaim verifiedRow ⟨2,1,0,29948,31936,10997349,259387791⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 29948 1989 ⟨10998424,259386716⟩
  rw [← get_eq_raw]
  exact (append (widen s29948_4 (by decide)) (append (widen s29952_256 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (widen s31936_1 (by decide))))))))

theorem claim638 : CheckedClaim verifiedRow ⟨2,1,0,29980,31968,6598559,256095620⟩ := by
  change Run (rawBlock verifiedRow 2 1 .value) 29980 1989 ⟨6599634,256094545⟩
  rw [← get_eq_raw]
  exact (append (widen s29980_4 (by decide)) (append (widen s29984_32 (by decide)) (append (widen s30016_64 (by decide)) (append (widen s30080_128 (by decide)) (append (widen s30208_512 (by decide)) (append (widen s30720_1024 (by decide)) (append (widen s31744_128 (by decide)) (append (widen s31872_64 (by decide)) (append (widen s31936_32 (by decide)) (widen s31968_1 (by decide)))))))))))

end GaussianChains.Point22.Atlas.RangeTicks
