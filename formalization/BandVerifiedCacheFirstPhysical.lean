import BandVerifiedCacheFirstRow
import BandVerifiedCacheProof0
import BandVerifiedCacheValidity
import BandVerifiedCacheOracleSound

/-! An end-to-end exclusion on the actual narrow slab and the first support. -/
namespace GaussianChains.Band.Fast

theorem first_row_excluded : RowExcluded .narrow ⟨0, by decide⟩ 0 := by
  let C := packetCache .narrow
  have hv : Valid .narrow C := packetCache_valid .narrow checkedAnchor0
  apply rowExcluded_of_tree .narrow ⟨0, by decide⟩ 0 4 firstTree
    (test := realTest .narrow C (Slab.narrow.floor ⟨0, by decide⟩) (support 0)) first_row_checked
  intro s h hs hw hf h0 h6 j B w u pass hm hu _ _
  apply realTest_sound .narrow C hv hw _ _ j hf h0 h6.le hm hu w pass
  exact WidthBounds.matched_hasDerivAt (a := (Slab.narrow.anchor:ℝ)) hs 0

/-- Removing the first branch of this actual certificate leaves uncovered
points and fails the same tree checker regardless of its remaining witnesses. -/
theorem first_row_missing_branch (rest : Cover Witness) :
    check (realTest .narrow (packetCache .narrow) (Slab.narrow.floor ⟨0, by decide⟩)
      (support 0) 4) (initial (support 0)) (.split 0 (grid 2048) .hole rest) = false := by
  simp [check]

#print axioms first_row_excluded
#print axioms first_row_missing_branch

end GaussianChains.Band.Fast
