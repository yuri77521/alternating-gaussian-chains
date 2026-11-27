import BandVerifiedCacheClaims

namespace GaussianChains.Band.Fast.Anchor2Part0

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_0 : runChecks (validatePage 2) 4 0 = true := by decide +kernel
private theorem rec_4_16 : runChecks (validatePage 2) 4 16 = true := by decide +kernel
private theorem rec_4_32 : runChecks (validatePage 2) 4 32 = true := by decide +kernel
private theorem rec_4_48 : runChecks (validatePage 2) 4 48 = true := by decide +kernel
private theorem rec_4_64 : runChecks (validatePage 2) 4 64 = true := by decide +kernel
private theorem rec_4_80 : runChecks (validatePage 2) 4 80 = true := by decide +kernel
private theorem rec_4_96 : runChecks (validatePage 2) 4 96 = true := by decide +kernel
private theorem rec_4_112 : runChecks (validatePage 2) 4 112 = true := by decide +kernel
private theorem rec_5_0 : runChecks (validatePage 2) 5 0 = true := runChecks_join rec_4_0 rec_4_16
private theorem rec_5_32 : runChecks (validatePage 2) 5 32 = true := runChecks_join rec_4_32 rec_4_48
private theorem rec_5_64 : runChecks (validatePage 2) 5 64 = true := runChecks_join rec_4_64 rec_4_80
private theorem rec_5_96 : runChecks (validatePage 2) 5 96 = true := runChecks_join rec_4_96 rec_4_112
private theorem rec_6_0 : runChecks (validatePage 2) 6 0 = true := runChecks_join rec_5_0 rec_5_32
private theorem rec_6_64 : runChecks (validatePage 2) 6 64 = true := runChecks_join rec_5_64 rec_5_96
private theorem rec_7_0 : runChecks (validatePage 2) 7 0 = true := runChecks_join rec_6_0 rec_6_64
theorem recurrence : runChecks (validatePage 2) 7 0 = true := rec_7_0

private theorem grid_5_0 : runChecks (validateNode 2) 5 0 = true := by decide +kernel
private theorem grid_5_32 : runChecks (validateNode 2) 5 32 = true := by decide +kernel
private theorem grid_5_64 : runChecks (validateNode 2) 5 64 = true := by decide +kernel
private theorem grid_5_96 : runChecks (validateNode 2) 5 96 = true := by decide +kernel
private theorem grid_5_128 : runChecks (validateNode 2) 5 128 = true := by decide +kernel
private theorem grid_5_160 : runChecks (validateNode 2) 5 160 = true := by decide +kernel
private theorem grid_5_192 : runChecks (validateNode 2) 5 192 = true := by decide +kernel
private theorem grid_5_224 : runChecks (validateNode 2) 5 224 = true := by decide +kernel
private theorem grid_5_256 : runChecks (validateNode 2) 5 256 = true := by decide +kernel
private theorem grid_5_288 : runChecks (validateNode 2) 5 288 = true := by decide +kernel
private theorem grid_5_320 : runChecks (validateNode 2) 5 320 = true := by decide +kernel
private theorem grid_5_352 : runChecks (validateNode 2) 5 352 = true := by decide +kernel
private theorem grid_5_384 : runChecks (validateNode 2) 5 384 = true := by decide +kernel
private theorem grid_5_416 : runChecks (validateNode 2) 5 416 = true := by decide +kernel
private theorem grid_5_448 : runChecks (validateNode 2) 5 448 = true := by decide +kernel
private theorem grid_5_480 : runChecks (validateNode 2) 5 480 = true := by decide +kernel
private theorem grid_5_512 : runChecks (validateNode 2) 5 512 = true := by decide +kernel
private theorem grid_5_544 : runChecks (validateNode 2) 5 544 = true := by decide +kernel
private theorem grid_5_576 : runChecks (validateNode 2) 5 576 = true := by decide +kernel
private theorem grid_5_608 : runChecks (validateNode 2) 5 608 = true := by decide +kernel
private theorem grid_5_640 : runChecks (validateNode 2) 5 640 = true := by decide +kernel
private theorem grid_5_672 : runChecks (validateNode 2) 5 672 = true := by decide +kernel
private theorem grid_5_704 : runChecks (validateNode 2) 5 704 = true := by decide +kernel
private theorem grid_5_736 : runChecks (validateNode 2) 5 736 = true := by decide +kernel
private theorem grid_5_768 : runChecks (validateNode 2) 5 768 = true := by decide +kernel
private theorem grid_5_800 : runChecks (validateNode 2) 5 800 = true := by decide +kernel
private theorem grid_5_832 : runChecks (validateNode 2) 5 832 = true := by decide +kernel
private theorem grid_5_864 : runChecks (validateNode 2) 5 864 = true := by decide +kernel
private theorem grid_5_896 : runChecks (validateNode 2) 5 896 = true := by decide +kernel
private theorem grid_5_928 : runChecks (validateNode 2) 5 928 = true := by decide +kernel
private theorem grid_5_960 : runChecks (validateNode 2) 5 960 = true := by decide +kernel
private theorem grid_5_992 : runChecks (validateNode 2) 5 992 = true := by decide +kernel
private theorem grid_6_0 : runChecks (validateNode 2) 6 0 = true := runChecks_join grid_5_0 grid_5_32
private theorem grid_6_64 : runChecks (validateNode 2) 6 64 = true := runChecks_join grid_5_64 grid_5_96
private theorem grid_6_128 : runChecks (validateNode 2) 6 128 = true := runChecks_join grid_5_128 grid_5_160
private theorem grid_6_192 : runChecks (validateNode 2) 6 192 = true := runChecks_join grid_5_192 grid_5_224
private theorem grid_6_256 : runChecks (validateNode 2) 6 256 = true := runChecks_join grid_5_256 grid_5_288
private theorem grid_6_320 : runChecks (validateNode 2) 6 320 = true := runChecks_join grid_5_320 grid_5_352
private theorem grid_6_384 : runChecks (validateNode 2) 6 384 = true := runChecks_join grid_5_384 grid_5_416
private theorem grid_6_448 : runChecks (validateNode 2) 6 448 = true := runChecks_join grid_5_448 grid_5_480
private theorem grid_6_512 : runChecks (validateNode 2) 6 512 = true := runChecks_join grid_5_512 grid_5_544
private theorem grid_6_576 : runChecks (validateNode 2) 6 576 = true := runChecks_join grid_5_576 grid_5_608
private theorem grid_6_640 : runChecks (validateNode 2) 6 640 = true := runChecks_join grid_5_640 grid_5_672
private theorem grid_6_704 : runChecks (validateNode 2) 6 704 = true := runChecks_join grid_5_704 grid_5_736
private theorem grid_6_768 : runChecks (validateNode 2) 6 768 = true := runChecks_join grid_5_768 grid_5_800
private theorem grid_6_832 : runChecks (validateNode 2) 6 832 = true := runChecks_join grid_5_832 grid_5_864
private theorem grid_6_896 : runChecks (validateNode 2) 6 896 = true := runChecks_join grid_5_896 grid_5_928
private theorem grid_6_960 : runChecks (validateNode 2) 6 960 = true := runChecks_join grid_5_960 grid_5_992
private theorem grid_7_0 : runChecks (validateNode 2) 7 0 = true := runChecks_join grid_6_0 grid_6_64
private theorem grid_7_128 : runChecks (validateNode 2) 7 128 = true := runChecks_join grid_6_128 grid_6_192
private theorem grid_7_256 : runChecks (validateNode 2) 7 256 = true := runChecks_join grid_6_256 grid_6_320
private theorem grid_7_384 : runChecks (validateNode 2) 7 384 = true := runChecks_join grid_6_384 grid_6_448
private theorem grid_7_512 : runChecks (validateNode 2) 7 512 = true := runChecks_join grid_6_512 grid_6_576
private theorem grid_7_640 : runChecks (validateNode 2) 7 640 = true := runChecks_join grid_6_640 grid_6_704
private theorem grid_7_768 : runChecks (validateNode 2) 7 768 = true := runChecks_join grid_6_768 grid_6_832
private theorem grid_7_896 : runChecks (validateNode 2) 7 896 = true := runChecks_join grid_6_896 grid_6_960
private theorem grid_8_0 : runChecks (validateNode 2) 8 0 = true := runChecks_join grid_7_0 grid_7_128
private theorem grid_8_256 : runChecks (validateNode 2) 8 256 = true := runChecks_join grid_7_256 grid_7_384
private theorem grid_8_512 : runChecks (validateNode 2) 8 512 = true := runChecks_join grid_7_512 grid_7_640
private theorem grid_8_768 : runChecks (validateNode 2) 8 768 = true := runChecks_join grid_7_768 grid_7_896
private theorem grid_9_0 : runChecks (validateNode 2) 9 0 = true := runChecks_join grid_8_0 grid_8_256
private theorem grid_9_512 : runChecks (validateNode 2) 9 512 = true := runChecks_join grid_8_512 grid_8_768
private theorem grid_10_0 : runChecks (validateNode 2) 10 0 = true := runChecks_join grid_9_0 grid_9_512
theorem nodes : runChecks (validateNode 2) 10 0 = true := grid_10_0

end GaussianChains.Band.Fast.Anchor2Part0
