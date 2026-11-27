import BandVerifiedCacheProof1Part0

namespace GaussianChains.Band.Fast.Anchor1Part1

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_128 : runChecks (validatePage 1) 4 128 = true := by decide +kernel
private theorem rec_4_144 : runChecks (validatePage 1) 4 144 = true := by decide +kernel
private theorem rec_4_160 : runChecks (validatePage 1) 4 160 = true := by decide +kernel
private theorem rec_4_176 : runChecks (validatePage 1) 4 176 = true := by decide +kernel
private theorem rec_4_192 : runChecks (validatePage 1) 4 192 = true := by decide +kernel
private theorem rec_4_208 : runChecks (validatePage 1) 4 208 = true := by decide +kernel
private theorem rec_4_224 : runChecks (validatePage 1) 4 224 = true := by decide +kernel
private theorem rec_4_240 : runChecks (validatePage 1) 4 240 = true := by decide +kernel
private theorem rec_5_128 : runChecks (validatePage 1) 5 128 = true := runChecks_join rec_4_128 rec_4_144
private theorem rec_5_160 : runChecks (validatePage 1) 5 160 = true := runChecks_join rec_4_160 rec_4_176
private theorem rec_5_192 : runChecks (validatePage 1) 5 192 = true := runChecks_join rec_4_192 rec_4_208
private theorem rec_5_224 : runChecks (validatePage 1) 5 224 = true := runChecks_join rec_4_224 rec_4_240
private theorem rec_6_128 : runChecks (validatePage 1) 6 128 = true := runChecks_join rec_5_128 rec_5_160
private theorem rec_6_192 : runChecks (validatePage 1) 6 192 = true := runChecks_join rec_5_192 rec_5_224
private theorem rec_7_128 : runChecks (validatePage 1) 7 128 = true := runChecks_join rec_6_128 rec_6_192
theorem recurrence : runChecks (validatePage 1) 7 128 = true := rec_7_128

private theorem grid_5_1024 : runChecks (validateNode 1) 5 1024 = true := by decide +kernel
private theorem grid_5_1056 : runChecks (validateNode 1) 5 1056 = true := by decide +kernel
private theorem grid_5_1088 : runChecks (validateNode 1) 5 1088 = true := by decide +kernel
private theorem grid_5_1120 : runChecks (validateNode 1) 5 1120 = true := by decide +kernel
private theorem grid_5_1152 : runChecks (validateNode 1) 5 1152 = true := by decide +kernel
private theorem grid_5_1184 : runChecks (validateNode 1) 5 1184 = true := by decide +kernel
private theorem grid_5_1216 : runChecks (validateNode 1) 5 1216 = true := by decide +kernel
private theorem grid_5_1248 : runChecks (validateNode 1) 5 1248 = true := by decide +kernel
private theorem grid_5_1280 : runChecks (validateNode 1) 5 1280 = true := by decide +kernel
private theorem grid_5_1312 : runChecks (validateNode 1) 5 1312 = true := by decide +kernel
private theorem grid_5_1344 : runChecks (validateNode 1) 5 1344 = true := by decide +kernel
private theorem grid_5_1376 : runChecks (validateNode 1) 5 1376 = true := by decide +kernel
private theorem grid_5_1408 : runChecks (validateNode 1) 5 1408 = true := by decide +kernel
private theorem grid_5_1440 : runChecks (validateNode 1) 5 1440 = true := by decide +kernel
private theorem grid_5_1472 : runChecks (validateNode 1) 5 1472 = true := by decide +kernel
private theorem grid_5_1504 : runChecks (validateNode 1) 5 1504 = true := by decide +kernel
private theorem grid_5_1536 : runChecks (validateNode 1) 5 1536 = true := by decide +kernel
private theorem grid_5_1568 : runChecks (validateNode 1) 5 1568 = true := by decide +kernel
private theorem grid_5_1600 : runChecks (validateNode 1) 5 1600 = true := by decide +kernel
private theorem grid_5_1632 : runChecks (validateNode 1) 5 1632 = true := by decide +kernel
private theorem grid_5_1664 : runChecks (validateNode 1) 5 1664 = true := by decide +kernel
private theorem grid_5_1696 : runChecks (validateNode 1) 5 1696 = true := by decide +kernel
private theorem grid_5_1728 : runChecks (validateNode 1) 5 1728 = true := by decide +kernel
private theorem grid_5_1760 : runChecks (validateNode 1) 5 1760 = true := by decide +kernel
private theorem grid_5_1792 : runChecks (validateNode 1) 5 1792 = true := by decide +kernel
private theorem grid_5_1824 : runChecks (validateNode 1) 5 1824 = true := by decide +kernel
private theorem grid_5_1856 : runChecks (validateNode 1) 5 1856 = true := by decide +kernel
private theorem grid_5_1888 : runChecks (validateNode 1) 5 1888 = true := by decide +kernel
private theorem grid_5_1920 : runChecks (validateNode 1) 5 1920 = true := by decide +kernel
private theorem grid_5_1952 : runChecks (validateNode 1) 5 1952 = true := by decide +kernel
private theorem grid_5_1984 : runChecks (validateNode 1) 5 1984 = true := by decide +kernel
private theorem grid_5_2016 : runChecks (validateNode 1) 5 2016 = true := by decide +kernel
private theorem grid_6_1024 : runChecks (validateNode 1) 6 1024 = true := runChecks_join grid_5_1024 grid_5_1056
private theorem grid_6_1088 : runChecks (validateNode 1) 6 1088 = true := runChecks_join grid_5_1088 grid_5_1120
private theorem grid_6_1152 : runChecks (validateNode 1) 6 1152 = true := runChecks_join grid_5_1152 grid_5_1184
private theorem grid_6_1216 : runChecks (validateNode 1) 6 1216 = true := runChecks_join grid_5_1216 grid_5_1248
private theorem grid_6_1280 : runChecks (validateNode 1) 6 1280 = true := runChecks_join grid_5_1280 grid_5_1312
private theorem grid_6_1344 : runChecks (validateNode 1) 6 1344 = true := runChecks_join grid_5_1344 grid_5_1376
private theorem grid_6_1408 : runChecks (validateNode 1) 6 1408 = true := runChecks_join grid_5_1408 grid_5_1440
private theorem grid_6_1472 : runChecks (validateNode 1) 6 1472 = true := runChecks_join grid_5_1472 grid_5_1504
private theorem grid_6_1536 : runChecks (validateNode 1) 6 1536 = true := runChecks_join grid_5_1536 grid_5_1568
private theorem grid_6_1600 : runChecks (validateNode 1) 6 1600 = true := runChecks_join grid_5_1600 grid_5_1632
private theorem grid_6_1664 : runChecks (validateNode 1) 6 1664 = true := runChecks_join grid_5_1664 grid_5_1696
private theorem grid_6_1728 : runChecks (validateNode 1) 6 1728 = true := runChecks_join grid_5_1728 grid_5_1760
private theorem grid_6_1792 : runChecks (validateNode 1) 6 1792 = true := runChecks_join grid_5_1792 grid_5_1824
private theorem grid_6_1856 : runChecks (validateNode 1) 6 1856 = true := runChecks_join grid_5_1856 grid_5_1888
private theorem grid_6_1920 : runChecks (validateNode 1) 6 1920 = true := runChecks_join grid_5_1920 grid_5_1952
private theorem grid_6_1984 : runChecks (validateNode 1) 6 1984 = true := runChecks_join grid_5_1984 grid_5_2016
private theorem grid_7_1024 : runChecks (validateNode 1) 7 1024 = true := runChecks_join grid_6_1024 grid_6_1088
private theorem grid_7_1152 : runChecks (validateNode 1) 7 1152 = true := runChecks_join grid_6_1152 grid_6_1216
private theorem grid_7_1280 : runChecks (validateNode 1) 7 1280 = true := runChecks_join grid_6_1280 grid_6_1344
private theorem grid_7_1408 : runChecks (validateNode 1) 7 1408 = true := runChecks_join grid_6_1408 grid_6_1472
private theorem grid_7_1536 : runChecks (validateNode 1) 7 1536 = true := runChecks_join grid_6_1536 grid_6_1600
private theorem grid_7_1664 : runChecks (validateNode 1) 7 1664 = true := runChecks_join grid_6_1664 grid_6_1728
private theorem grid_7_1792 : runChecks (validateNode 1) 7 1792 = true := runChecks_join grid_6_1792 grid_6_1856
private theorem grid_7_1920 : runChecks (validateNode 1) 7 1920 = true := runChecks_join grid_6_1920 grid_6_1984
private theorem grid_8_1024 : runChecks (validateNode 1) 8 1024 = true := runChecks_join grid_7_1024 grid_7_1152
private theorem grid_8_1280 : runChecks (validateNode 1) 8 1280 = true := runChecks_join grid_7_1280 grid_7_1408
private theorem grid_8_1536 : runChecks (validateNode 1) 8 1536 = true := runChecks_join grid_7_1536 grid_7_1664
private theorem grid_8_1792 : runChecks (validateNode 1) 8 1792 = true := runChecks_join grid_7_1792 grid_7_1920
private theorem grid_9_1024 : runChecks (validateNode 1) 9 1024 = true := runChecks_join grid_8_1024 grid_8_1280
private theorem grid_9_1536 : runChecks (validateNode 1) 9 1536 = true := runChecks_join grid_8_1536 grid_8_1792
private theorem grid_10_1024 : runChecks (validateNode 1) 10 1024 = true := runChecks_join grid_9_1024 grid_9_1536
theorem nodes : runChecks (validateNode 1) 10 1024 = true := grid_10_1024

end GaussianChains.Band.Fast.Anchor1Part1
