import BandVerifiedCacheProof1Part6

namespace GaussianChains.Band.Fast.Anchor1Part7

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem rec_4_896 : runChecks (validatePage 1) 4 896 = true := by decide +kernel
private theorem rec_4_912 : runChecks (validatePage 1) 4 912 = true := by decide +kernel
private theorem rec_4_928 : runChecks (validatePage 1) 4 928 = true := by decide +kernel
private theorem rec_4_944 : runChecks (validatePage 1) 4 944 = true := by decide +kernel
private theorem rec_4_960 : runChecks (validatePage 1) 4 960 = true := by decide +kernel
private theorem rec_4_976 : runChecks (validatePage 1) 4 976 = true := by decide +kernel
private theorem rec_4_992 : runChecks (validatePage 1) 4 992 = true := by decide +kernel
private theorem rec_4_1008 : runChecks (validatePage 1) 4 1008 = true := by decide +kernel
private theorem rec_5_896 : runChecks (validatePage 1) 5 896 = true := runChecks_join rec_4_896 rec_4_912
private theorem rec_5_928 : runChecks (validatePage 1) 5 928 = true := runChecks_join rec_4_928 rec_4_944
private theorem rec_5_960 : runChecks (validatePage 1) 5 960 = true := runChecks_join rec_4_960 rec_4_976
private theorem rec_5_992 : runChecks (validatePage 1) 5 992 = true := runChecks_join rec_4_992 rec_4_1008
private theorem rec_6_896 : runChecks (validatePage 1) 6 896 = true := runChecks_join rec_5_896 rec_5_928
private theorem rec_6_960 : runChecks (validatePage 1) 6 960 = true := runChecks_join rec_5_960 rec_5_992
private theorem rec_7_896 : runChecks (validatePage 1) 7 896 = true := runChecks_join rec_6_896 rec_6_960
theorem recurrence : runChecks (validatePage 1) 7 896 = true := rec_7_896

private theorem grid_5_7168 : runChecks (validateNode 1) 5 7168 = true := by decide +kernel
private theorem grid_5_7200 : runChecks (validateNode 1) 5 7200 = true := by decide +kernel
private theorem grid_5_7232 : runChecks (validateNode 1) 5 7232 = true := by decide +kernel
private theorem grid_5_7264 : runChecks (validateNode 1) 5 7264 = true := by decide +kernel
private theorem grid_5_7296 : runChecks (validateNode 1) 5 7296 = true := by decide +kernel
private theorem grid_5_7328 : runChecks (validateNode 1) 5 7328 = true := by decide +kernel
private theorem grid_5_7360 : runChecks (validateNode 1) 5 7360 = true := by decide +kernel
private theorem grid_5_7392 : runChecks (validateNode 1) 5 7392 = true := by decide +kernel
private theorem grid_5_7424 : runChecks (validateNode 1) 5 7424 = true := by decide +kernel
private theorem grid_5_7456 : runChecks (validateNode 1) 5 7456 = true := by decide +kernel
private theorem grid_5_7488 : runChecks (validateNode 1) 5 7488 = true := by decide +kernel
private theorem grid_5_7520 : runChecks (validateNode 1) 5 7520 = true := by decide +kernel
private theorem grid_5_7552 : runChecks (validateNode 1) 5 7552 = true := by decide +kernel
private theorem grid_5_7584 : runChecks (validateNode 1) 5 7584 = true := by decide +kernel
private theorem grid_5_7616 : runChecks (validateNode 1) 5 7616 = true := by decide +kernel
private theorem grid_5_7648 : runChecks (validateNode 1) 5 7648 = true := by decide +kernel
private theorem grid_5_7680 : runChecks (validateNode 1) 5 7680 = true := by decide +kernel
private theorem grid_5_7712 : runChecks (validateNode 1) 5 7712 = true := by decide +kernel
private theorem grid_5_7744 : runChecks (validateNode 1) 5 7744 = true := by decide +kernel
private theorem grid_5_7776 : runChecks (validateNode 1) 5 7776 = true := by decide +kernel
private theorem grid_5_7808 : runChecks (validateNode 1) 5 7808 = true := by decide +kernel
private theorem grid_5_7840 : runChecks (validateNode 1) 5 7840 = true := by decide +kernel
private theorem grid_5_7872 : runChecks (validateNode 1) 5 7872 = true := by decide +kernel
private theorem grid_5_7904 : runChecks (validateNode 1) 5 7904 = true := by decide +kernel
private theorem grid_5_7936 : runChecks (validateNode 1) 5 7936 = true := by decide +kernel
private theorem grid_5_7968 : runChecks (validateNode 1) 5 7968 = true := by decide +kernel
private theorem grid_5_8000 : runChecks (validateNode 1) 5 8000 = true := by decide +kernel
private theorem grid_5_8032 : runChecks (validateNode 1) 5 8032 = true := by decide +kernel
private theorem grid_5_8064 : runChecks (validateNode 1) 5 8064 = true := by decide +kernel
private theorem grid_5_8096 : runChecks (validateNode 1) 5 8096 = true := by decide +kernel
private theorem grid_5_8128 : runChecks (validateNode 1) 5 8128 = true := by decide +kernel
private theorem grid_5_8160 : runChecks (validateNode 1) 5 8160 = true := by decide +kernel
private theorem grid_6_7168 : runChecks (validateNode 1) 6 7168 = true := runChecks_join grid_5_7168 grid_5_7200
private theorem grid_6_7232 : runChecks (validateNode 1) 6 7232 = true := runChecks_join grid_5_7232 grid_5_7264
private theorem grid_6_7296 : runChecks (validateNode 1) 6 7296 = true := runChecks_join grid_5_7296 grid_5_7328
private theorem grid_6_7360 : runChecks (validateNode 1) 6 7360 = true := runChecks_join grid_5_7360 grid_5_7392
private theorem grid_6_7424 : runChecks (validateNode 1) 6 7424 = true := runChecks_join grid_5_7424 grid_5_7456
private theorem grid_6_7488 : runChecks (validateNode 1) 6 7488 = true := runChecks_join grid_5_7488 grid_5_7520
private theorem grid_6_7552 : runChecks (validateNode 1) 6 7552 = true := runChecks_join grid_5_7552 grid_5_7584
private theorem grid_6_7616 : runChecks (validateNode 1) 6 7616 = true := runChecks_join grid_5_7616 grid_5_7648
private theorem grid_6_7680 : runChecks (validateNode 1) 6 7680 = true := runChecks_join grid_5_7680 grid_5_7712
private theorem grid_6_7744 : runChecks (validateNode 1) 6 7744 = true := runChecks_join grid_5_7744 grid_5_7776
private theorem grid_6_7808 : runChecks (validateNode 1) 6 7808 = true := runChecks_join grid_5_7808 grid_5_7840
private theorem grid_6_7872 : runChecks (validateNode 1) 6 7872 = true := runChecks_join grid_5_7872 grid_5_7904
private theorem grid_6_7936 : runChecks (validateNode 1) 6 7936 = true := runChecks_join grid_5_7936 grid_5_7968
private theorem grid_6_8000 : runChecks (validateNode 1) 6 8000 = true := runChecks_join grid_5_8000 grid_5_8032
private theorem grid_6_8064 : runChecks (validateNode 1) 6 8064 = true := runChecks_join grid_5_8064 grid_5_8096
private theorem grid_6_8128 : runChecks (validateNode 1) 6 8128 = true := runChecks_join grid_5_8128 grid_5_8160
private theorem grid_7_7168 : runChecks (validateNode 1) 7 7168 = true := runChecks_join grid_6_7168 grid_6_7232
private theorem grid_7_7296 : runChecks (validateNode 1) 7 7296 = true := runChecks_join grid_6_7296 grid_6_7360
private theorem grid_7_7424 : runChecks (validateNode 1) 7 7424 = true := runChecks_join grid_6_7424 grid_6_7488
private theorem grid_7_7552 : runChecks (validateNode 1) 7 7552 = true := runChecks_join grid_6_7552 grid_6_7616
private theorem grid_7_7680 : runChecks (validateNode 1) 7 7680 = true := runChecks_join grid_6_7680 grid_6_7744
private theorem grid_7_7808 : runChecks (validateNode 1) 7 7808 = true := runChecks_join grid_6_7808 grid_6_7872
private theorem grid_7_7936 : runChecks (validateNode 1) 7 7936 = true := runChecks_join grid_6_7936 grid_6_8000
private theorem grid_7_8064 : runChecks (validateNode 1) 7 8064 = true := runChecks_join grid_6_8064 grid_6_8128
private theorem grid_8_7168 : runChecks (validateNode 1) 8 7168 = true := runChecks_join grid_7_7168 grid_7_7296
private theorem grid_8_7424 : runChecks (validateNode 1) 8 7424 = true := runChecks_join grid_7_7424 grid_7_7552
private theorem grid_8_7680 : runChecks (validateNode 1) 8 7680 = true := runChecks_join grid_7_7680 grid_7_7808
private theorem grid_8_7936 : runChecks (validateNode 1) 8 7936 = true := runChecks_join grid_7_7936 grid_7_8064
private theorem grid_9_7168 : runChecks (validateNode 1) 9 7168 = true := runChecks_join grid_8_7168 grid_8_7424
private theorem grid_9_7680 : runChecks (validateNode 1) 9 7680 = true := runChecks_join grid_8_7680 grid_8_7936
private theorem grid_10_7168 : runChecks (validateNode 1) 10 7168 = true := runChecks_join grid_9_7168 grid_9_7680
theorem nodes : runChecks (validateNode 1) 10 7168 = true := grid_10_7168

end GaussianChains.Band.Fast.Anchor1Part7
