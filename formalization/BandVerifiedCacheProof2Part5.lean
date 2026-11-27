import BandVerifiedCacheProof2Part4

namespace GaussianChains.Band.Fast.Anchor2Part5

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_640 : runChecks (validatePage 2) 4 640 = true := by decide +kernel
private theorem rec_4_656 : runChecks (validatePage 2) 4 656 = true := by decide +kernel
private theorem rec_4_672 : runChecks (validatePage 2) 4 672 = true := by decide +kernel
private theorem rec_4_688 : runChecks (validatePage 2) 4 688 = true := by decide +kernel
private theorem rec_4_704 : runChecks (validatePage 2) 4 704 = true := by decide +kernel
private theorem rec_4_720 : runChecks (validatePage 2) 4 720 = true := by decide +kernel
private theorem rec_4_736 : runChecks (validatePage 2) 4 736 = true := by decide +kernel
private theorem rec_4_752 : runChecks (validatePage 2) 4 752 = true := by decide +kernel
private theorem rec_5_640 : runChecks (validatePage 2) 5 640 = true := runChecks_join rec_4_640 rec_4_656
private theorem rec_5_672 : runChecks (validatePage 2) 5 672 = true := runChecks_join rec_4_672 rec_4_688
private theorem rec_5_704 : runChecks (validatePage 2) 5 704 = true := runChecks_join rec_4_704 rec_4_720
private theorem rec_5_736 : runChecks (validatePage 2) 5 736 = true := runChecks_join rec_4_736 rec_4_752
private theorem rec_6_640 : runChecks (validatePage 2) 6 640 = true := runChecks_join rec_5_640 rec_5_672
private theorem rec_6_704 : runChecks (validatePage 2) 6 704 = true := runChecks_join rec_5_704 rec_5_736
private theorem rec_7_640 : runChecks (validatePage 2) 7 640 = true := runChecks_join rec_6_640 rec_6_704
theorem recurrence : runChecks (validatePage 2) 7 640 = true := rec_7_640

private theorem grid_5_5120 : runChecks (validateNode 2) 5 5120 = true := by decide +kernel
private theorem grid_5_5152 : runChecks (validateNode 2) 5 5152 = true := by decide +kernel
private theorem grid_5_5184 : runChecks (validateNode 2) 5 5184 = true := by decide +kernel
private theorem grid_5_5216 : runChecks (validateNode 2) 5 5216 = true := by decide +kernel
private theorem grid_5_5248 : runChecks (validateNode 2) 5 5248 = true := by decide +kernel
private theorem grid_5_5280 : runChecks (validateNode 2) 5 5280 = true := by decide +kernel
private theorem grid_5_5312 : runChecks (validateNode 2) 5 5312 = true := by decide +kernel
private theorem grid_5_5344 : runChecks (validateNode 2) 5 5344 = true := by decide +kernel
private theorem grid_5_5376 : runChecks (validateNode 2) 5 5376 = true := by decide +kernel
private theorem grid_5_5408 : runChecks (validateNode 2) 5 5408 = true := by decide +kernel
private theorem grid_5_5440 : runChecks (validateNode 2) 5 5440 = true := by decide +kernel
private theorem grid_5_5472 : runChecks (validateNode 2) 5 5472 = true := by decide +kernel
private theorem grid_5_5504 : runChecks (validateNode 2) 5 5504 = true := by decide +kernel
private theorem grid_5_5536 : runChecks (validateNode 2) 5 5536 = true := by decide +kernel
private theorem grid_5_5568 : runChecks (validateNode 2) 5 5568 = true := by decide +kernel
private theorem grid_5_5600 : runChecks (validateNode 2) 5 5600 = true := by decide +kernel
private theorem grid_5_5632 : runChecks (validateNode 2) 5 5632 = true := by decide +kernel
private theorem grid_5_5664 : runChecks (validateNode 2) 5 5664 = true := by decide +kernel
private theorem grid_5_5696 : runChecks (validateNode 2) 5 5696 = true := by decide +kernel
private theorem grid_5_5728 : runChecks (validateNode 2) 5 5728 = true := by decide +kernel
private theorem grid_5_5760 : runChecks (validateNode 2) 5 5760 = true := by decide +kernel
private theorem grid_5_5792 : runChecks (validateNode 2) 5 5792 = true := by decide +kernel
private theorem grid_5_5824 : runChecks (validateNode 2) 5 5824 = true := by decide +kernel
private theorem grid_5_5856 : runChecks (validateNode 2) 5 5856 = true := by decide +kernel
private theorem grid_5_5888 : runChecks (validateNode 2) 5 5888 = true := by decide +kernel
private theorem grid_5_5920 : runChecks (validateNode 2) 5 5920 = true := by decide +kernel
private theorem grid_5_5952 : runChecks (validateNode 2) 5 5952 = true := by decide +kernel
private theorem grid_5_5984 : runChecks (validateNode 2) 5 5984 = true := by decide +kernel
private theorem grid_5_6016 : runChecks (validateNode 2) 5 6016 = true := by decide +kernel
private theorem grid_5_6048 : runChecks (validateNode 2) 5 6048 = true := by decide +kernel
private theorem grid_5_6080 : runChecks (validateNode 2) 5 6080 = true := by decide +kernel
private theorem grid_5_6112 : runChecks (validateNode 2) 5 6112 = true := by decide +kernel
private theorem grid_6_5120 : runChecks (validateNode 2) 6 5120 = true := runChecks_join grid_5_5120 grid_5_5152
private theorem grid_6_5184 : runChecks (validateNode 2) 6 5184 = true := runChecks_join grid_5_5184 grid_5_5216
private theorem grid_6_5248 : runChecks (validateNode 2) 6 5248 = true := runChecks_join grid_5_5248 grid_5_5280
private theorem grid_6_5312 : runChecks (validateNode 2) 6 5312 = true := runChecks_join grid_5_5312 grid_5_5344
private theorem grid_6_5376 : runChecks (validateNode 2) 6 5376 = true := runChecks_join grid_5_5376 grid_5_5408
private theorem grid_6_5440 : runChecks (validateNode 2) 6 5440 = true := runChecks_join grid_5_5440 grid_5_5472
private theorem grid_6_5504 : runChecks (validateNode 2) 6 5504 = true := runChecks_join grid_5_5504 grid_5_5536
private theorem grid_6_5568 : runChecks (validateNode 2) 6 5568 = true := runChecks_join grid_5_5568 grid_5_5600
private theorem grid_6_5632 : runChecks (validateNode 2) 6 5632 = true := runChecks_join grid_5_5632 grid_5_5664
private theorem grid_6_5696 : runChecks (validateNode 2) 6 5696 = true := runChecks_join grid_5_5696 grid_5_5728
private theorem grid_6_5760 : runChecks (validateNode 2) 6 5760 = true := runChecks_join grid_5_5760 grid_5_5792
private theorem grid_6_5824 : runChecks (validateNode 2) 6 5824 = true := runChecks_join grid_5_5824 grid_5_5856
private theorem grid_6_5888 : runChecks (validateNode 2) 6 5888 = true := runChecks_join grid_5_5888 grid_5_5920
private theorem grid_6_5952 : runChecks (validateNode 2) 6 5952 = true := runChecks_join grid_5_5952 grid_5_5984
private theorem grid_6_6016 : runChecks (validateNode 2) 6 6016 = true := runChecks_join grid_5_6016 grid_5_6048
private theorem grid_6_6080 : runChecks (validateNode 2) 6 6080 = true := runChecks_join grid_5_6080 grid_5_6112
private theorem grid_7_5120 : runChecks (validateNode 2) 7 5120 = true := runChecks_join grid_6_5120 grid_6_5184
private theorem grid_7_5248 : runChecks (validateNode 2) 7 5248 = true := runChecks_join grid_6_5248 grid_6_5312
private theorem grid_7_5376 : runChecks (validateNode 2) 7 5376 = true := runChecks_join grid_6_5376 grid_6_5440
private theorem grid_7_5504 : runChecks (validateNode 2) 7 5504 = true := runChecks_join grid_6_5504 grid_6_5568
private theorem grid_7_5632 : runChecks (validateNode 2) 7 5632 = true := runChecks_join grid_6_5632 grid_6_5696
private theorem grid_7_5760 : runChecks (validateNode 2) 7 5760 = true := runChecks_join grid_6_5760 grid_6_5824
private theorem grid_7_5888 : runChecks (validateNode 2) 7 5888 = true := runChecks_join grid_6_5888 grid_6_5952
private theorem grid_7_6016 : runChecks (validateNode 2) 7 6016 = true := runChecks_join grid_6_6016 grid_6_6080
private theorem grid_8_5120 : runChecks (validateNode 2) 8 5120 = true := runChecks_join grid_7_5120 grid_7_5248
private theorem grid_8_5376 : runChecks (validateNode 2) 8 5376 = true := runChecks_join grid_7_5376 grid_7_5504
private theorem grid_8_5632 : runChecks (validateNode 2) 8 5632 = true := runChecks_join grid_7_5632 grid_7_5760
private theorem grid_8_5888 : runChecks (validateNode 2) 8 5888 = true := runChecks_join grid_7_5888 grid_7_6016
private theorem grid_9_5120 : runChecks (validateNode 2) 9 5120 = true := runChecks_join grid_8_5120 grid_8_5376
private theorem grid_9_5632 : runChecks (validateNode 2) 9 5632 = true := runChecks_join grid_8_5632 grid_8_5888
private theorem grid_10_5120 : runChecks (validateNode 2) 10 5120 = true := runChecks_join grid_9_5120 grid_9_5632
theorem nodes : runChecks (validateNode 2) 10 5120 = true := grid_10_5120

end GaussianChains.Band.Fast.Anchor2Part5
