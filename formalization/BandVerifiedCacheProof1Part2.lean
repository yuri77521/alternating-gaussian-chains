import BandVerifiedCacheProof1Part1

namespace GaussianChains.Band.Fast.Anchor1Part2

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_256 : runChecks (validatePage 1) 4 256 = true := by decide +kernel
private theorem rec_4_272 : runChecks (validatePage 1) 4 272 = true := by decide +kernel
private theorem rec_4_288 : runChecks (validatePage 1) 4 288 = true := by decide +kernel
private theorem rec_4_304 : runChecks (validatePage 1) 4 304 = true := by decide +kernel
private theorem rec_4_320 : runChecks (validatePage 1) 4 320 = true := by decide +kernel
private theorem rec_4_336 : runChecks (validatePage 1) 4 336 = true := by decide +kernel
private theorem rec_4_352 : runChecks (validatePage 1) 4 352 = true := by decide +kernel
private theorem rec_4_368 : runChecks (validatePage 1) 4 368 = true := by decide +kernel
private theorem rec_5_256 : runChecks (validatePage 1) 5 256 = true := runChecks_join rec_4_256 rec_4_272
private theorem rec_5_288 : runChecks (validatePage 1) 5 288 = true := runChecks_join rec_4_288 rec_4_304
private theorem rec_5_320 : runChecks (validatePage 1) 5 320 = true := runChecks_join rec_4_320 rec_4_336
private theorem rec_5_352 : runChecks (validatePage 1) 5 352 = true := runChecks_join rec_4_352 rec_4_368
private theorem rec_6_256 : runChecks (validatePage 1) 6 256 = true := runChecks_join rec_5_256 rec_5_288
private theorem rec_6_320 : runChecks (validatePage 1) 6 320 = true := runChecks_join rec_5_320 rec_5_352
private theorem rec_7_256 : runChecks (validatePage 1) 7 256 = true := runChecks_join rec_6_256 rec_6_320
theorem recurrence : runChecks (validatePage 1) 7 256 = true := rec_7_256

private theorem grid_5_2048 : runChecks (validateNode 1) 5 2048 = true := by decide +kernel
private theorem grid_5_2080 : runChecks (validateNode 1) 5 2080 = true := by decide +kernel
private theorem grid_5_2112 : runChecks (validateNode 1) 5 2112 = true := by decide +kernel
private theorem grid_5_2144 : runChecks (validateNode 1) 5 2144 = true := by decide +kernel
private theorem grid_5_2176 : runChecks (validateNode 1) 5 2176 = true := by decide +kernel
private theorem grid_5_2208 : runChecks (validateNode 1) 5 2208 = true := by decide +kernel
private theorem grid_5_2240 : runChecks (validateNode 1) 5 2240 = true := by decide +kernel
private theorem grid_5_2272 : runChecks (validateNode 1) 5 2272 = true := by decide +kernel
private theorem grid_5_2304 : runChecks (validateNode 1) 5 2304 = true := by decide +kernel
private theorem grid_5_2336 : runChecks (validateNode 1) 5 2336 = true := by decide +kernel
private theorem grid_5_2368 : runChecks (validateNode 1) 5 2368 = true := by decide +kernel
private theorem grid_5_2400 : runChecks (validateNode 1) 5 2400 = true := by decide +kernel
private theorem grid_5_2432 : runChecks (validateNode 1) 5 2432 = true := by decide +kernel
private theorem grid_5_2464 : runChecks (validateNode 1) 5 2464 = true := by decide +kernel
private theorem grid_5_2496 : runChecks (validateNode 1) 5 2496 = true := by decide +kernel
private theorem grid_5_2528 : runChecks (validateNode 1) 5 2528 = true := by decide +kernel
private theorem grid_5_2560 : runChecks (validateNode 1) 5 2560 = true := by decide +kernel
private theorem grid_5_2592 : runChecks (validateNode 1) 5 2592 = true := by decide +kernel
private theorem grid_5_2624 : runChecks (validateNode 1) 5 2624 = true := by decide +kernel
private theorem grid_5_2656 : runChecks (validateNode 1) 5 2656 = true := by decide +kernel
private theorem grid_5_2688 : runChecks (validateNode 1) 5 2688 = true := by decide +kernel
private theorem grid_5_2720 : runChecks (validateNode 1) 5 2720 = true := by decide +kernel
private theorem grid_5_2752 : runChecks (validateNode 1) 5 2752 = true := by decide +kernel
private theorem grid_5_2784 : runChecks (validateNode 1) 5 2784 = true := by decide +kernel
private theorem grid_5_2816 : runChecks (validateNode 1) 5 2816 = true := by decide +kernel
private theorem grid_5_2848 : runChecks (validateNode 1) 5 2848 = true := by decide +kernel
private theorem grid_5_2880 : runChecks (validateNode 1) 5 2880 = true := by decide +kernel
private theorem grid_5_2912 : runChecks (validateNode 1) 5 2912 = true := by decide +kernel
private theorem grid_5_2944 : runChecks (validateNode 1) 5 2944 = true := by decide +kernel
private theorem grid_5_2976 : runChecks (validateNode 1) 5 2976 = true := by decide +kernel
private theorem grid_5_3008 : runChecks (validateNode 1) 5 3008 = true := by decide +kernel
private theorem grid_5_3040 : runChecks (validateNode 1) 5 3040 = true := by decide +kernel
private theorem grid_6_2048 : runChecks (validateNode 1) 6 2048 = true := runChecks_join grid_5_2048 grid_5_2080
private theorem grid_6_2112 : runChecks (validateNode 1) 6 2112 = true := runChecks_join grid_5_2112 grid_5_2144
private theorem grid_6_2176 : runChecks (validateNode 1) 6 2176 = true := runChecks_join grid_5_2176 grid_5_2208
private theorem grid_6_2240 : runChecks (validateNode 1) 6 2240 = true := runChecks_join grid_5_2240 grid_5_2272
private theorem grid_6_2304 : runChecks (validateNode 1) 6 2304 = true := runChecks_join grid_5_2304 grid_5_2336
private theorem grid_6_2368 : runChecks (validateNode 1) 6 2368 = true := runChecks_join grid_5_2368 grid_5_2400
private theorem grid_6_2432 : runChecks (validateNode 1) 6 2432 = true := runChecks_join grid_5_2432 grid_5_2464
private theorem grid_6_2496 : runChecks (validateNode 1) 6 2496 = true := runChecks_join grid_5_2496 grid_5_2528
private theorem grid_6_2560 : runChecks (validateNode 1) 6 2560 = true := runChecks_join grid_5_2560 grid_5_2592
private theorem grid_6_2624 : runChecks (validateNode 1) 6 2624 = true := runChecks_join grid_5_2624 grid_5_2656
private theorem grid_6_2688 : runChecks (validateNode 1) 6 2688 = true := runChecks_join grid_5_2688 grid_5_2720
private theorem grid_6_2752 : runChecks (validateNode 1) 6 2752 = true := runChecks_join grid_5_2752 grid_5_2784
private theorem grid_6_2816 : runChecks (validateNode 1) 6 2816 = true := runChecks_join grid_5_2816 grid_5_2848
private theorem grid_6_2880 : runChecks (validateNode 1) 6 2880 = true := runChecks_join grid_5_2880 grid_5_2912
private theorem grid_6_2944 : runChecks (validateNode 1) 6 2944 = true := runChecks_join grid_5_2944 grid_5_2976
private theorem grid_6_3008 : runChecks (validateNode 1) 6 3008 = true := runChecks_join grid_5_3008 grid_5_3040
private theorem grid_7_2048 : runChecks (validateNode 1) 7 2048 = true := runChecks_join grid_6_2048 grid_6_2112
private theorem grid_7_2176 : runChecks (validateNode 1) 7 2176 = true := runChecks_join grid_6_2176 grid_6_2240
private theorem grid_7_2304 : runChecks (validateNode 1) 7 2304 = true := runChecks_join grid_6_2304 grid_6_2368
private theorem grid_7_2432 : runChecks (validateNode 1) 7 2432 = true := runChecks_join grid_6_2432 grid_6_2496
private theorem grid_7_2560 : runChecks (validateNode 1) 7 2560 = true := runChecks_join grid_6_2560 grid_6_2624
private theorem grid_7_2688 : runChecks (validateNode 1) 7 2688 = true := runChecks_join grid_6_2688 grid_6_2752
private theorem grid_7_2816 : runChecks (validateNode 1) 7 2816 = true := runChecks_join grid_6_2816 grid_6_2880
private theorem grid_7_2944 : runChecks (validateNode 1) 7 2944 = true := runChecks_join grid_6_2944 grid_6_3008
private theorem grid_8_2048 : runChecks (validateNode 1) 8 2048 = true := runChecks_join grid_7_2048 grid_7_2176
private theorem grid_8_2304 : runChecks (validateNode 1) 8 2304 = true := runChecks_join grid_7_2304 grid_7_2432
private theorem grid_8_2560 : runChecks (validateNode 1) 8 2560 = true := runChecks_join grid_7_2560 grid_7_2688
private theorem grid_8_2816 : runChecks (validateNode 1) 8 2816 = true := runChecks_join grid_7_2816 grid_7_2944
private theorem grid_9_2048 : runChecks (validateNode 1) 9 2048 = true := runChecks_join grid_8_2048 grid_8_2304
private theorem grid_9_2560 : runChecks (validateNode 1) 9 2560 = true := runChecks_join grid_8_2560 grid_8_2816
private theorem grid_10_2048 : runChecks (validateNode 1) 10 2048 = true := runChecks_join grid_9_2048 grid_9_2560
theorem nodes : runChecks (validateNode 1) 10 2048 = true := grid_10_2048

end GaussianChains.Band.Fast.Anchor1Part2
