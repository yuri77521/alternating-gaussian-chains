import BandVerifiedCacheProof0Part3

namespace GaussianChains.Band.Fast.Anchor0Part4

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_512 : runChecks (validatePage 0) 4 512 = true := by decide +kernel
private theorem rec_4_528 : runChecks (validatePage 0) 4 528 = true := by decide +kernel
private theorem rec_4_544 : runChecks (validatePage 0) 4 544 = true := by decide +kernel
private theorem rec_4_560 : runChecks (validatePage 0) 4 560 = true := by decide +kernel
private theorem rec_4_576 : runChecks (validatePage 0) 4 576 = true := by decide +kernel
private theorem rec_4_592 : runChecks (validatePage 0) 4 592 = true := by decide +kernel
private theorem rec_4_608 : runChecks (validatePage 0) 4 608 = true := by decide +kernel
private theorem rec_4_624 : runChecks (validatePage 0) 4 624 = true := by decide +kernel
private theorem rec_5_512 : runChecks (validatePage 0) 5 512 = true := runChecks_join rec_4_512 rec_4_528
private theorem rec_5_544 : runChecks (validatePage 0) 5 544 = true := runChecks_join rec_4_544 rec_4_560
private theorem rec_5_576 : runChecks (validatePage 0) 5 576 = true := runChecks_join rec_4_576 rec_4_592
private theorem rec_5_608 : runChecks (validatePage 0) 5 608 = true := runChecks_join rec_4_608 rec_4_624
private theorem rec_6_512 : runChecks (validatePage 0) 6 512 = true := runChecks_join rec_5_512 rec_5_544
private theorem rec_6_576 : runChecks (validatePage 0) 6 576 = true := runChecks_join rec_5_576 rec_5_608
private theorem rec_7_512 : runChecks (validatePage 0) 7 512 = true := runChecks_join rec_6_512 rec_6_576
theorem recurrence : runChecks (validatePage 0) 7 512 = true := rec_7_512

private theorem grid_5_4096 : runChecks (validateNode 0) 5 4096 = true := by decide +kernel
private theorem grid_5_4128 : runChecks (validateNode 0) 5 4128 = true := by decide +kernel
private theorem grid_5_4160 : runChecks (validateNode 0) 5 4160 = true := by decide +kernel
private theorem grid_5_4192 : runChecks (validateNode 0) 5 4192 = true := by decide +kernel
private theorem grid_5_4224 : runChecks (validateNode 0) 5 4224 = true := by decide +kernel
private theorem grid_5_4256 : runChecks (validateNode 0) 5 4256 = true := by decide +kernel
private theorem grid_5_4288 : runChecks (validateNode 0) 5 4288 = true := by decide +kernel
private theorem grid_5_4320 : runChecks (validateNode 0) 5 4320 = true := by decide +kernel
private theorem grid_5_4352 : runChecks (validateNode 0) 5 4352 = true := by decide +kernel
private theorem grid_5_4384 : runChecks (validateNode 0) 5 4384 = true := by decide +kernel
private theorem grid_5_4416 : runChecks (validateNode 0) 5 4416 = true := by decide +kernel
private theorem grid_5_4448 : runChecks (validateNode 0) 5 4448 = true := by decide +kernel
private theorem grid_5_4480 : runChecks (validateNode 0) 5 4480 = true := by decide +kernel
private theorem grid_5_4512 : runChecks (validateNode 0) 5 4512 = true := by decide +kernel
private theorem grid_5_4544 : runChecks (validateNode 0) 5 4544 = true := by decide +kernel
private theorem grid_5_4576 : runChecks (validateNode 0) 5 4576 = true := by decide +kernel
private theorem grid_5_4608 : runChecks (validateNode 0) 5 4608 = true := by decide +kernel
private theorem grid_5_4640 : runChecks (validateNode 0) 5 4640 = true := by decide +kernel
private theorem grid_5_4672 : runChecks (validateNode 0) 5 4672 = true := by decide +kernel
private theorem grid_5_4704 : runChecks (validateNode 0) 5 4704 = true := by decide +kernel
private theorem grid_5_4736 : runChecks (validateNode 0) 5 4736 = true := by decide +kernel
private theorem grid_5_4768 : runChecks (validateNode 0) 5 4768 = true := by decide +kernel
private theorem grid_5_4800 : runChecks (validateNode 0) 5 4800 = true := by decide +kernel
private theorem grid_5_4832 : runChecks (validateNode 0) 5 4832 = true := by decide +kernel
private theorem grid_5_4864 : runChecks (validateNode 0) 5 4864 = true := by decide +kernel
private theorem grid_5_4896 : runChecks (validateNode 0) 5 4896 = true := by decide +kernel
private theorem grid_5_4928 : runChecks (validateNode 0) 5 4928 = true := by decide +kernel
private theorem grid_5_4960 : runChecks (validateNode 0) 5 4960 = true := by decide +kernel
private theorem grid_5_4992 : runChecks (validateNode 0) 5 4992 = true := by decide +kernel
private theorem grid_5_5024 : runChecks (validateNode 0) 5 5024 = true := by decide +kernel
private theorem grid_5_5056 : runChecks (validateNode 0) 5 5056 = true := by decide +kernel
private theorem grid_5_5088 : runChecks (validateNode 0) 5 5088 = true := by decide +kernel
private theorem grid_6_4096 : runChecks (validateNode 0) 6 4096 = true := runChecks_join grid_5_4096 grid_5_4128
private theorem grid_6_4160 : runChecks (validateNode 0) 6 4160 = true := runChecks_join grid_5_4160 grid_5_4192
private theorem grid_6_4224 : runChecks (validateNode 0) 6 4224 = true := runChecks_join grid_5_4224 grid_5_4256
private theorem grid_6_4288 : runChecks (validateNode 0) 6 4288 = true := runChecks_join grid_5_4288 grid_5_4320
private theorem grid_6_4352 : runChecks (validateNode 0) 6 4352 = true := runChecks_join grid_5_4352 grid_5_4384
private theorem grid_6_4416 : runChecks (validateNode 0) 6 4416 = true := runChecks_join grid_5_4416 grid_5_4448
private theorem grid_6_4480 : runChecks (validateNode 0) 6 4480 = true := runChecks_join grid_5_4480 grid_5_4512
private theorem grid_6_4544 : runChecks (validateNode 0) 6 4544 = true := runChecks_join grid_5_4544 grid_5_4576
private theorem grid_6_4608 : runChecks (validateNode 0) 6 4608 = true := runChecks_join grid_5_4608 grid_5_4640
private theorem grid_6_4672 : runChecks (validateNode 0) 6 4672 = true := runChecks_join grid_5_4672 grid_5_4704
private theorem grid_6_4736 : runChecks (validateNode 0) 6 4736 = true := runChecks_join grid_5_4736 grid_5_4768
private theorem grid_6_4800 : runChecks (validateNode 0) 6 4800 = true := runChecks_join grid_5_4800 grid_5_4832
private theorem grid_6_4864 : runChecks (validateNode 0) 6 4864 = true := runChecks_join grid_5_4864 grid_5_4896
private theorem grid_6_4928 : runChecks (validateNode 0) 6 4928 = true := runChecks_join grid_5_4928 grid_5_4960
private theorem grid_6_4992 : runChecks (validateNode 0) 6 4992 = true := runChecks_join grid_5_4992 grid_5_5024
private theorem grid_6_5056 : runChecks (validateNode 0) 6 5056 = true := runChecks_join grid_5_5056 grid_5_5088
private theorem grid_7_4096 : runChecks (validateNode 0) 7 4096 = true := runChecks_join grid_6_4096 grid_6_4160
private theorem grid_7_4224 : runChecks (validateNode 0) 7 4224 = true := runChecks_join grid_6_4224 grid_6_4288
private theorem grid_7_4352 : runChecks (validateNode 0) 7 4352 = true := runChecks_join grid_6_4352 grid_6_4416
private theorem grid_7_4480 : runChecks (validateNode 0) 7 4480 = true := runChecks_join grid_6_4480 grid_6_4544
private theorem grid_7_4608 : runChecks (validateNode 0) 7 4608 = true := runChecks_join grid_6_4608 grid_6_4672
private theorem grid_7_4736 : runChecks (validateNode 0) 7 4736 = true := runChecks_join grid_6_4736 grid_6_4800
private theorem grid_7_4864 : runChecks (validateNode 0) 7 4864 = true := runChecks_join grid_6_4864 grid_6_4928
private theorem grid_7_4992 : runChecks (validateNode 0) 7 4992 = true := runChecks_join grid_6_4992 grid_6_5056
private theorem grid_8_4096 : runChecks (validateNode 0) 8 4096 = true := runChecks_join grid_7_4096 grid_7_4224
private theorem grid_8_4352 : runChecks (validateNode 0) 8 4352 = true := runChecks_join grid_7_4352 grid_7_4480
private theorem grid_8_4608 : runChecks (validateNode 0) 8 4608 = true := runChecks_join grid_7_4608 grid_7_4736
private theorem grid_8_4864 : runChecks (validateNode 0) 8 4864 = true := runChecks_join grid_7_4864 grid_7_4992
private theorem grid_9_4096 : runChecks (validateNode 0) 9 4096 = true := runChecks_join grid_8_4096 grid_8_4352
private theorem grid_9_4608 : runChecks (validateNode 0) 9 4608 = true := runChecks_join grid_8_4608 grid_8_4864
private theorem grid_10_4096 : runChecks (validateNode 0) 10 4096 = true := runChecks_join grid_9_4096 grid_9_4608
theorem nodes : runChecks (validateNode 0) 10 4096 = true := grid_10_4096

end GaussianChains.Band.Fast.Anchor0Part4
