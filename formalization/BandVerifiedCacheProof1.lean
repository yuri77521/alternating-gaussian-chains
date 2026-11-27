import BandVerifiedCacheProof1Part7

namespace GaussianChains.Band.Fast

set_option Elab.async false
set_option maxRecDepth 100000

private theorem rec_8_0 : runChecks (validatePage 1) 8 0 = true := runChecks_join Anchor1Part0.recurrence Anchor1Part1.recurrence
private theorem rec_8_256 : runChecks (validatePage 1) 8 256 = true := runChecks_join Anchor1Part2.recurrence Anchor1Part3.recurrence
private theorem rec_8_512 : runChecks (validatePage 1) 8 512 = true := runChecks_join Anchor1Part4.recurrence Anchor1Part5.recurrence
private theorem rec_8_768 : runChecks (validatePage 1) 8 768 = true := runChecks_join Anchor1Part6.recurrence Anchor1Part7.recurrence
private theorem rec_9_0 : runChecks (validatePage 1) 9 0 = true := runChecks_join rec_8_0 rec_8_256
private theorem rec_9_512 : runChecks (validatePage 1) 9 512 = true := runChecks_join rec_8_512 rec_8_768
private theorem rec_10_0 : runChecks (validatePage 1) 10 0 = true := runChecks_join rec_9_0 rec_9_512
private theorem grid_11_0 : runChecks (validateNode 1) 11 0 = true := runChecks_join Anchor1Part0.nodes Anchor1Part1.nodes
private theorem grid_11_2048 : runChecks (validateNode 1) 11 2048 = true := runChecks_join Anchor1Part2.nodes Anchor1Part3.nodes
private theorem grid_11_4096 : runChecks (validateNode 1) 11 4096 = true := runChecks_join Anchor1Part4.nodes Anchor1Part5.nodes
private theorem grid_11_6144 : runChecks (validateNode 1) 11 6144 = true := runChecks_join Anchor1Part6.nodes Anchor1Part7.nodes
private theorem grid_12_0 : runChecks (validateNode 1) 12 0 = true := runChecks_join grid_11_0 grid_11_2048
private theorem grid_12_4096 : runChecks (validateNode 1) 12 4096 = true := runChecks_join grid_11_4096 grid_11_6144
private theorem grid_13_0 : runChecks (validateNode 1) 13 0 = true := runChecks_join grid_12_0 grid_12_4096

theorem checkedAnchor1 : Checked 1 where
  init := by decide +kernel
  recurrence := rec_10_0
  grid := grid_13_0
  last := by decide +kernel

#print axioms checkedAnchor1

end GaussianChains.Band.Fast
