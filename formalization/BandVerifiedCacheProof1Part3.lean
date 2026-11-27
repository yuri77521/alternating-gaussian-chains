import BandVerifiedCacheProof1Part2

namespace GaussianChains.Band.Fast.Anchor1Part3

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_384 : runChecks (validatePage 1) 4 384 = true := by decide +kernel
private theorem rec_4_400 : runChecks (validatePage 1) 4 400 = true := by decide +kernel
private theorem rec_4_416 : runChecks (validatePage 1) 4 416 = true := by decide +kernel
private theorem rec_4_432 : runChecks (validatePage 1) 4 432 = true := by decide +kernel
private theorem rec_4_448 : runChecks (validatePage 1) 4 448 = true := by decide +kernel
private theorem rec_4_464 : runChecks (validatePage 1) 4 464 = true := by decide +kernel
private theorem rec_4_480 : runChecks (validatePage 1) 4 480 = true := by decide +kernel
private theorem rec_4_496 : runChecks (validatePage 1) 4 496 = true := by decide +kernel
private theorem rec_5_384 : runChecks (validatePage 1) 5 384 = true := runChecks_join rec_4_384 rec_4_400
private theorem rec_5_416 : runChecks (validatePage 1) 5 416 = true := runChecks_join rec_4_416 rec_4_432
private theorem rec_5_448 : runChecks (validatePage 1) 5 448 = true := runChecks_join rec_4_448 rec_4_464
private theorem rec_5_480 : runChecks (validatePage 1) 5 480 = true := runChecks_join rec_4_480 rec_4_496
private theorem rec_6_384 : runChecks (validatePage 1) 6 384 = true := runChecks_join rec_5_384 rec_5_416
private theorem rec_6_448 : runChecks (validatePage 1) 6 448 = true := runChecks_join rec_5_448 rec_5_480
private theorem rec_7_384 : runChecks (validatePage 1) 7 384 = true := runChecks_join rec_6_384 rec_6_448
theorem recurrence : runChecks (validatePage 1) 7 384 = true := rec_7_384

private theorem grid_5_3072 : runChecks (validateNode 1) 5 3072 = true := by decide +kernel
private theorem grid_5_3104 : runChecks (validateNode 1) 5 3104 = true := by decide +kernel
private theorem grid_5_3136 : runChecks (validateNode 1) 5 3136 = true := by decide +kernel
private theorem grid_5_3168 : runChecks (validateNode 1) 5 3168 = true := by decide +kernel
private theorem grid_5_3200 : runChecks (validateNode 1) 5 3200 = true := by decide +kernel
private theorem grid_5_3232 : runChecks (validateNode 1) 5 3232 = true := by decide +kernel
private theorem grid_5_3264 : runChecks (validateNode 1) 5 3264 = true := by decide +kernel
private theorem grid_5_3296 : runChecks (validateNode 1) 5 3296 = true := by decide +kernel
private theorem grid_5_3328 : runChecks (validateNode 1) 5 3328 = true := by decide +kernel
private theorem grid_5_3360 : runChecks (validateNode 1) 5 3360 = true := by decide +kernel
private theorem grid_5_3392 : runChecks (validateNode 1) 5 3392 = true := by decide +kernel
private theorem grid_5_3424 : runChecks (validateNode 1) 5 3424 = true := by decide +kernel
private theorem grid_5_3456 : runChecks (validateNode 1) 5 3456 = true := by decide +kernel
private theorem grid_5_3488 : runChecks (validateNode 1) 5 3488 = true := by decide +kernel
private theorem grid_5_3520 : runChecks (validateNode 1) 5 3520 = true := by decide +kernel
private theorem grid_5_3552 : runChecks (validateNode 1) 5 3552 = true := by decide +kernel
private theorem grid_5_3584 : runChecks (validateNode 1) 5 3584 = true := by decide +kernel
private theorem grid_5_3616 : runChecks (validateNode 1) 5 3616 = true := by decide +kernel
private theorem grid_5_3648 : runChecks (validateNode 1) 5 3648 = true := by decide +kernel
private theorem grid_5_3680 : runChecks (validateNode 1) 5 3680 = true := by decide +kernel
private theorem grid_5_3712 : runChecks (validateNode 1) 5 3712 = true := by decide +kernel
private theorem grid_5_3744 : runChecks (validateNode 1) 5 3744 = true := by decide +kernel
private theorem grid_5_3776 : runChecks (validateNode 1) 5 3776 = true := by decide +kernel
private theorem grid_5_3808 : runChecks (validateNode 1) 5 3808 = true := by decide +kernel
private theorem grid_5_3840 : runChecks (validateNode 1) 5 3840 = true := by decide +kernel
private theorem grid_5_3872 : runChecks (validateNode 1) 5 3872 = true := by decide +kernel
private theorem grid_5_3904 : runChecks (validateNode 1) 5 3904 = true := by decide +kernel
private theorem grid_5_3936 : runChecks (validateNode 1) 5 3936 = true := by decide +kernel
private theorem grid_5_3968 : runChecks (validateNode 1) 5 3968 = true := by decide +kernel
private theorem grid_5_4000 : runChecks (validateNode 1) 5 4000 = true := by decide +kernel
private theorem grid_5_4032 : runChecks (validateNode 1) 5 4032 = true := by decide +kernel
private theorem grid_5_4064 : runChecks (validateNode 1) 5 4064 = true := by decide +kernel
private theorem grid_6_3072 : runChecks (validateNode 1) 6 3072 = true := runChecks_join grid_5_3072 grid_5_3104
private theorem grid_6_3136 : runChecks (validateNode 1) 6 3136 = true := runChecks_join grid_5_3136 grid_5_3168
private theorem grid_6_3200 : runChecks (validateNode 1) 6 3200 = true := runChecks_join grid_5_3200 grid_5_3232
private theorem grid_6_3264 : runChecks (validateNode 1) 6 3264 = true := runChecks_join grid_5_3264 grid_5_3296
private theorem grid_6_3328 : runChecks (validateNode 1) 6 3328 = true := runChecks_join grid_5_3328 grid_5_3360
private theorem grid_6_3392 : runChecks (validateNode 1) 6 3392 = true := runChecks_join grid_5_3392 grid_5_3424
private theorem grid_6_3456 : runChecks (validateNode 1) 6 3456 = true := runChecks_join grid_5_3456 grid_5_3488
private theorem grid_6_3520 : runChecks (validateNode 1) 6 3520 = true := runChecks_join grid_5_3520 grid_5_3552
private theorem grid_6_3584 : runChecks (validateNode 1) 6 3584 = true := runChecks_join grid_5_3584 grid_5_3616
private theorem grid_6_3648 : runChecks (validateNode 1) 6 3648 = true := runChecks_join grid_5_3648 grid_5_3680
private theorem grid_6_3712 : runChecks (validateNode 1) 6 3712 = true := runChecks_join grid_5_3712 grid_5_3744
private theorem grid_6_3776 : runChecks (validateNode 1) 6 3776 = true := runChecks_join grid_5_3776 grid_5_3808
private theorem grid_6_3840 : runChecks (validateNode 1) 6 3840 = true := runChecks_join grid_5_3840 grid_5_3872
private theorem grid_6_3904 : runChecks (validateNode 1) 6 3904 = true := runChecks_join grid_5_3904 grid_5_3936
private theorem grid_6_3968 : runChecks (validateNode 1) 6 3968 = true := runChecks_join grid_5_3968 grid_5_4000
private theorem grid_6_4032 : runChecks (validateNode 1) 6 4032 = true := runChecks_join grid_5_4032 grid_5_4064
private theorem grid_7_3072 : runChecks (validateNode 1) 7 3072 = true := runChecks_join grid_6_3072 grid_6_3136
private theorem grid_7_3200 : runChecks (validateNode 1) 7 3200 = true := runChecks_join grid_6_3200 grid_6_3264
private theorem grid_7_3328 : runChecks (validateNode 1) 7 3328 = true := runChecks_join grid_6_3328 grid_6_3392
private theorem grid_7_3456 : runChecks (validateNode 1) 7 3456 = true := runChecks_join grid_6_3456 grid_6_3520
private theorem grid_7_3584 : runChecks (validateNode 1) 7 3584 = true := runChecks_join grid_6_3584 grid_6_3648
private theorem grid_7_3712 : runChecks (validateNode 1) 7 3712 = true := runChecks_join grid_6_3712 grid_6_3776
private theorem grid_7_3840 : runChecks (validateNode 1) 7 3840 = true := runChecks_join grid_6_3840 grid_6_3904
private theorem grid_7_3968 : runChecks (validateNode 1) 7 3968 = true := runChecks_join grid_6_3968 grid_6_4032
private theorem grid_8_3072 : runChecks (validateNode 1) 8 3072 = true := runChecks_join grid_7_3072 grid_7_3200
private theorem grid_8_3328 : runChecks (validateNode 1) 8 3328 = true := runChecks_join grid_7_3328 grid_7_3456
private theorem grid_8_3584 : runChecks (validateNode 1) 8 3584 = true := runChecks_join grid_7_3584 grid_7_3712
private theorem grid_8_3840 : runChecks (validateNode 1) 8 3840 = true := runChecks_join grid_7_3840 grid_7_3968
private theorem grid_9_3072 : runChecks (validateNode 1) 9 3072 = true := runChecks_join grid_8_3072 grid_8_3328
private theorem grid_9_3584 : runChecks (validateNode 1) 9 3584 = true := runChecks_join grid_8_3584 grid_8_3840
private theorem grid_10_3072 : runChecks (validateNode 1) 10 3072 = true := runChecks_join grid_9_3072 grid_9_3584
theorem nodes : runChecks (validateNode 1) 10 3072 = true := grid_10_3072

end GaussianChains.Band.Fast.Anchor1Part3
