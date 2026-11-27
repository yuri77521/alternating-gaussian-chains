import BandVerifiedCacheProof2Part5

namespace GaussianChains.Band.Fast.Anchor2Part6

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_768 : runChecks (validatePage 2) 4 768 = true := by decide +kernel
private theorem rec_4_784 : runChecks (validatePage 2) 4 784 = true := by decide +kernel
private theorem rec_4_800 : runChecks (validatePage 2) 4 800 = true := by decide +kernel
private theorem rec_4_816 : runChecks (validatePage 2) 4 816 = true := by decide +kernel
private theorem rec_4_832 : runChecks (validatePage 2) 4 832 = true := by decide +kernel
private theorem rec_4_848 : runChecks (validatePage 2) 4 848 = true := by decide +kernel
private theorem rec_4_864 : runChecks (validatePage 2) 4 864 = true := by decide +kernel
private theorem rec_4_880 : runChecks (validatePage 2) 4 880 = true := by decide +kernel
private theorem rec_5_768 : runChecks (validatePage 2) 5 768 = true := runChecks_join rec_4_768 rec_4_784
private theorem rec_5_800 : runChecks (validatePage 2) 5 800 = true := runChecks_join rec_4_800 rec_4_816
private theorem rec_5_832 : runChecks (validatePage 2) 5 832 = true := runChecks_join rec_4_832 rec_4_848
private theorem rec_5_864 : runChecks (validatePage 2) 5 864 = true := runChecks_join rec_4_864 rec_4_880
private theorem rec_6_768 : runChecks (validatePage 2) 6 768 = true := runChecks_join rec_5_768 rec_5_800
private theorem rec_6_832 : runChecks (validatePage 2) 6 832 = true := runChecks_join rec_5_832 rec_5_864
private theorem rec_7_768 : runChecks (validatePage 2) 7 768 = true := runChecks_join rec_6_768 rec_6_832
theorem recurrence : runChecks (validatePage 2) 7 768 = true := rec_7_768

private theorem grid_5_6144 : runChecks (validateNode 2) 5 6144 = true := by decide +kernel
private theorem grid_5_6176 : runChecks (validateNode 2) 5 6176 = true := by decide +kernel
private theorem grid_5_6208 : runChecks (validateNode 2) 5 6208 = true := by decide +kernel
private theorem grid_5_6240 : runChecks (validateNode 2) 5 6240 = true := by decide +kernel
private theorem grid_5_6272 : runChecks (validateNode 2) 5 6272 = true := by decide +kernel
private theorem grid_5_6304 : runChecks (validateNode 2) 5 6304 = true := by decide +kernel
private theorem grid_5_6336 : runChecks (validateNode 2) 5 6336 = true := by decide +kernel
private theorem grid_5_6368 : runChecks (validateNode 2) 5 6368 = true := by decide +kernel
private theorem grid_5_6400 : runChecks (validateNode 2) 5 6400 = true := by decide +kernel
private theorem grid_5_6432 : runChecks (validateNode 2) 5 6432 = true := by decide +kernel
private theorem grid_5_6464 : runChecks (validateNode 2) 5 6464 = true := by decide +kernel
private theorem grid_5_6496 : runChecks (validateNode 2) 5 6496 = true := by decide +kernel
private theorem grid_5_6528 : runChecks (validateNode 2) 5 6528 = true := by decide +kernel
private theorem grid_5_6560 : runChecks (validateNode 2) 5 6560 = true := by decide +kernel
private theorem grid_5_6592 : runChecks (validateNode 2) 5 6592 = true := by decide +kernel
private theorem grid_5_6624 : runChecks (validateNode 2) 5 6624 = true := by decide +kernel
private theorem grid_5_6656 : runChecks (validateNode 2) 5 6656 = true := by decide +kernel
private theorem grid_5_6688 : runChecks (validateNode 2) 5 6688 = true := by decide +kernel
private theorem grid_5_6720 : runChecks (validateNode 2) 5 6720 = true := by decide +kernel
private theorem grid_5_6752 : runChecks (validateNode 2) 5 6752 = true := by decide +kernel
private theorem grid_5_6784 : runChecks (validateNode 2) 5 6784 = true := by decide +kernel
private theorem grid_5_6816 : runChecks (validateNode 2) 5 6816 = true := by decide +kernel
private theorem grid_5_6848 : runChecks (validateNode 2) 5 6848 = true := by decide +kernel
private theorem grid_5_6880 : runChecks (validateNode 2) 5 6880 = true := by decide +kernel
private theorem grid_5_6912 : runChecks (validateNode 2) 5 6912 = true := by decide +kernel
private theorem grid_5_6944 : runChecks (validateNode 2) 5 6944 = true := by decide +kernel
private theorem grid_5_6976 : runChecks (validateNode 2) 5 6976 = true := by decide +kernel
private theorem grid_5_7008 : runChecks (validateNode 2) 5 7008 = true := by decide +kernel
private theorem grid_5_7040 : runChecks (validateNode 2) 5 7040 = true := by decide +kernel
private theorem grid_5_7072 : runChecks (validateNode 2) 5 7072 = true := by decide +kernel
private theorem grid_5_7104 : runChecks (validateNode 2) 5 7104 = true := by decide +kernel
private theorem grid_5_7136 : runChecks (validateNode 2) 5 7136 = true := by decide +kernel
private theorem grid_6_6144 : runChecks (validateNode 2) 6 6144 = true := runChecks_join grid_5_6144 grid_5_6176
private theorem grid_6_6208 : runChecks (validateNode 2) 6 6208 = true := runChecks_join grid_5_6208 grid_5_6240
private theorem grid_6_6272 : runChecks (validateNode 2) 6 6272 = true := runChecks_join grid_5_6272 grid_5_6304
private theorem grid_6_6336 : runChecks (validateNode 2) 6 6336 = true := runChecks_join grid_5_6336 grid_5_6368
private theorem grid_6_6400 : runChecks (validateNode 2) 6 6400 = true := runChecks_join grid_5_6400 grid_5_6432
private theorem grid_6_6464 : runChecks (validateNode 2) 6 6464 = true := runChecks_join grid_5_6464 grid_5_6496
private theorem grid_6_6528 : runChecks (validateNode 2) 6 6528 = true := runChecks_join grid_5_6528 grid_5_6560
private theorem grid_6_6592 : runChecks (validateNode 2) 6 6592 = true := runChecks_join grid_5_6592 grid_5_6624
private theorem grid_6_6656 : runChecks (validateNode 2) 6 6656 = true := runChecks_join grid_5_6656 grid_5_6688
private theorem grid_6_6720 : runChecks (validateNode 2) 6 6720 = true := runChecks_join grid_5_6720 grid_5_6752
private theorem grid_6_6784 : runChecks (validateNode 2) 6 6784 = true := runChecks_join grid_5_6784 grid_5_6816
private theorem grid_6_6848 : runChecks (validateNode 2) 6 6848 = true := runChecks_join grid_5_6848 grid_5_6880
private theorem grid_6_6912 : runChecks (validateNode 2) 6 6912 = true := runChecks_join grid_5_6912 grid_5_6944
private theorem grid_6_6976 : runChecks (validateNode 2) 6 6976 = true := runChecks_join grid_5_6976 grid_5_7008
private theorem grid_6_7040 : runChecks (validateNode 2) 6 7040 = true := runChecks_join grid_5_7040 grid_5_7072
private theorem grid_6_7104 : runChecks (validateNode 2) 6 7104 = true := runChecks_join grid_5_7104 grid_5_7136
private theorem grid_7_6144 : runChecks (validateNode 2) 7 6144 = true := runChecks_join grid_6_6144 grid_6_6208
private theorem grid_7_6272 : runChecks (validateNode 2) 7 6272 = true := runChecks_join grid_6_6272 grid_6_6336
private theorem grid_7_6400 : runChecks (validateNode 2) 7 6400 = true := runChecks_join grid_6_6400 grid_6_6464
private theorem grid_7_6528 : runChecks (validateNode 2) 7 6528 = true := runChecks_join grid_6_6528 grid_6_6592
private theorem grid_7_6656 : runChecks (validateNode 2) 7 6656 = true := runChecks_join grid_6_6656 grid_6_6720
private theorem grid_7_6784 : runChecks (validateNode 2) 7 6784 = true := runChecks_join grid_6_6784 grid_6_6848
private theorem grid_7_6912 : runChecks (validateNode 2) 7 6912 = true := runChecks_join grid_6_6912 grid_6_6976
private theorem grid_7_7040 : runChecks (validateNode 2) 7 7040 = true := runChecks_join grid_6_7040 grid_6_7104
private theorem grid_8_6144 : runChecks (validateNode 2) 8 6144 = true := runChecks_join grid_7_6144 grid_7_6272
private theorem grid_8_6400 : runChecks (validateNode 2) 8 6400 = true := runChecks_join grid_7_6400 grid_7_6528
private theorem grid_8_6656 : runChecks (validateNode 2) 8 6656 = true := runChecks_join grid_7_6656 grid_7_6784
private theorem grid_8_6912 : runChecks (validateNode 2) 8 6912 = true := runChecks_join grid_7_6912 grid_7_7040
private theorem grid_9_6144 : runChecks (validateNode 2) 9 6144 = true := runChecks_join grid_8_6144 grid_8_6400
private theorem grid_9_6656 : runChecks (validateNode 2) 9 6656 = true := runChecks_join grid_8_6656 grid_8_6912
private theorem grid_10_6144 : runChecks (validateNode 2) 10 6144 = true := runChecks_join grid_9_6144 grid_9_6656
theorem nodes : runChecks (validateNode 2) 10 6144 = true := grid_10_6144

end GaussianChains.Band.Fast.Anchor2Part6
