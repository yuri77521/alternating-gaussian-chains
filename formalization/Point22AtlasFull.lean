import Point22AtlasWords
import Point22AtlasRangeChecked
import Point22AtlasTablesChecked
import Point22AtlasRangesSound
import Point22AtlasScoreNumbers
import Point22FromAtlas

/-! All numerical evidence for the eleven excluded words and the six local terminal
boxes of 3111, coupled to the independently defined continuum score and its variations. -/
namespace GaussianChains.Point22.Atlas

open GaussianChains.Cert GaussianChains.ImageBounds

theorem all_range_claims_valid : ∀ c ∈ claimIndex.entries, RangeValid c := by
  intro c hc
  apply checkedClaim_valid (node := Tables.verifiedRow) (fun j p hp => Tables.verifiedRow_sound j hp)
  exact RangeTicks.checked_claimIndex c hc

/-- Full atlas consequence for canonical block starts, including ties in their allowed
wrapped gaps. Every numerical test in the antecedent-free lookup has been discharged. -/
theorem atlas_localizes {w : Word} {x : Fin 6 → ℝ}
    (ho : OrderedTicks w x) (hc : CanonicalTicks w x) (hs : SpanTicks w x)
    (hx : (rootBox w).Mem x)
    (htrial : pairScore 22 (fun i => (Root22.witnessX i : ℝ)) ≤
      atlasScore w (meshToPhysical x) (internalScore w))
    (hmax : ∀ v : Fin 6 → ℝ,
      IsLocalMax (fun t => atlasScore w (blockTranslation (meshToPhysical x) v t) (internalScore w)) 0) :
    w = .threeOneOneOne ∧ localTarget.Mem x := by
  apply classify_of_replay (lookup := checkedLookup) (internal := internalTicks)
    (witness := witnessTicks) (checkedLookup_sound all_range_claims_valid)
    (internalTicks_sound w) witnessTicks_sound ho hc hs hx _ (all_words_accept w)
  exact realQuantity_necessary w _ _ _ htrial hmax

#print axioms atlas_localizes

/-- The independent twelve-word atlas captures every physical ground state
in the local uniqueness region, with no numerical premise. -/
theorem physical_localize_all_words (x : Fin 6 → ℝ)
    (hx : IsGroundState (by decide) (1/1000) 22 x) : LocalizedAt x (1/1000) :=
  physical_localize_of_replay (checkedLookup_sound all_range_claims_valid)
    internalTicks_sound witnessTicks_sound all_words_accept x hx

#print axioms physical_localize_all_words
end GaussianChains.Point22.Atlas
