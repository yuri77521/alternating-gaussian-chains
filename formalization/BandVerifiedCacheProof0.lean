import BandVerifiedCacheProof0Part7

namespace GaussianChains.Band.Fast

set_option Elab.async false
set_option maxRecDepth 100000

private theorem rec_8_0 : runChecks (validatePage 0) 8 0 = true := runChecks_join Anchor0Part0.recurrence Anchor0Part1.recurrence
private theorem rec_8_256 : runChecks (validatePage 0) 8 256 = true := runChecks_join Anchor0Part2.recurrence Anchor0Part3.recurrence
private theorem rec_8_512 : runChecks (validatePage 0) 8 512 = true := runChecks_join Anchor0Part4.recurrence Anchor0Part5.recurrence
private theorem rec_8_768 : runChecks (validatePage 0) 8 768 = true := runChecks_join Anchor0Part6.recurrence Anchor0Part7.recurrence
private theorem rec_9_0 : runChecks (validatePage 0) 9 0 = true := runChecks_join rec_8_0 rec_8_256
private theorem rec_9_512 : runChecks (validatePage 0) 9 512 = true := runChecks_join rec_8_512 rec_8_768
private theorem rec_10_0 : runChecks (validatePage 0) 10 0 = true := runChecks_join rec_9_0 rec_9_512
private theorem grid_11_0 : runChecks (validateNode 0) 11 0 = true := runChecks_join Anchor0Part0.nodes Anchor0Part1.nodes
private theorem grid_11_2048 : runChecks (validateNode 0) 11 2048 = true := runChecks_join Anchor0Part2.nodes Anchor0Part3.nodes
private theorem grid_11_4096 : runChecks (validateNode 0) 11 4096 = true := runChecks_join Anchor0Part4.nodes Anchor0Part5.nodes
private theorem grid_11_6144 : runChecks (validateNode 0) 11 6144 = true := runChecks_join Anchor0Part6.nodes Anchor0Part7.nodes
private theorem grid_12_0 : runChecks (validateNode 0) 12 0 = true := runChecks_join grid_11_0 grid_11_2048
private theorem grid_12_4096 : runChecks (validateNode 0) 12 4096 = true := runChecks_join grid_11_4096 grid_11_6144
private theorem grid_13_0 : runChecks (validateNode 0) 13 0 = true := runChecks_join grid_12_0 grid_12_4096

theorem checkedAnchor0 : Checked 0 where
  init := by decide +kernel
  recurrence := rec_10_0
  grid := grid_13_0
  last := by decide +kernel

#print axioms checkedAnchor0

end GaussianChains.Band.Fast
