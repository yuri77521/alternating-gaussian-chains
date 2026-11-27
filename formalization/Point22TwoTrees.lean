import Point22TwoTreeLookup
import Point22FromAtlas
import Point22Interior
import Point22NineWords
import Point22AtlasWord21111
import Point22AtlasWord3111
import Point22AtlasScoreNumbers

/-! At s=22 and h=1/1000 ten of the twelve actual contact words have analytic
exclusions. The two remaining tree replays use only the 11, 21, and 31 block ranges. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert GaussianChains.ImageBounds Root22

/-- Exact support, including the last gap, narrows any minimizer to two words
before using a box table. A cut at a tied largest slack gap is allowed. -/
theorem ground_word_cases (w : Word) (z : Fin 6 → ℝ)
    (hz : IsGroundState (by decide) (1/1000) 22 z)
    (hc : CanonicalBlockCut w (gap (by decide) z)) :
    w = .twoOneOneOneOne ∨ w = .threeOneOneOne := by
  have hm : matchesWord (actualCuts (1/1000) (gap (by decide) z)) w = true := by
    apply (matchesWord_iff _ _).2
    exact ⟨0,false,fun i => by simpa [edgeIndex] using hc.1 i⟩
  have hd : w.twoDisjointContacts = false := by
    cases he : w.twoDisjointContacts with
    | false => rfl
    | true => exact False.elim (disjoint_word_ne_ground_state z hm he hz)
  have remaining (v : Word) : v.twoDisjointContacts = false →
      v = .singletons ∨ v = .twoOneOneOneOne ∨ v = .threeOneOneOne := by
    cases v <;> decide
  rcases remaining w hd with rfl | h
  · exfalso
    apply Interior.all_slack_excluded z _ hz
    intro i
    have he := (hc.1 i).trans
      ((by decide : ∀ i : Fin 6, Word.singletons.cuts i = true) i)
    exact of_decide_eq_true he
  · exact h

/-- Continuous-domain capture by the analytic ten-word exclusions and the two
remaining numerical trees. The only table premise is validity of stored closed
ranges for the three ordered block-size pairs used on these two words. -/
theorem physical_localize_two_trees
    (ranges : ∀ c ∈ claimIndex.entries, TwoTreePair c.a c.b → RangeValid c)
    (x : Fin 6 → ℝ) (hx : IsGroundState (by decide) (1/1000) 22 x) : LocalizedAt x (1/1000) := by
  apply physical_localize_of_admissible_replays (twoTreeLookup_sound ranges)
    internalTicks_sound witnessTicks_sound _ x hx
  intro w z hz hc
  have hw := ground_word_cases w z hz hc
  rw [twoTreeBounds_eq hw]
  rcases hw with rfl | rfl
  · exact word21111_accept
  · exact word3111_accept

#print axioms ground_word_cases
#print axioms physical_localize_two_trees
end GaussianChains.Point22.Atlas
