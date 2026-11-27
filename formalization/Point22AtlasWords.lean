import Point22AtlasWord2211Page0
import Point22AtlasWord3111
import Point22AtlasWord21111
import Point22AtlasWord111111

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem all_words_accept (w : Word) : atlasAccept w = true := by
  cases w with
  | six => exact six_block_accept
  | threeThree => exact two_triples_accept
  | fourTwo => exact w42OK
  | fiveOne => exact w51OK
  | twoTwoTwo => exact w222OK
  | threeTwoOne => exact w321OK
  | fourOneOne => exact w411OK
  | twoOneTwoOne => exact w2121OK
  | twoTwoOneOne => exact w2211OK
  | threeOneOneOne => exact w3111OK
  | twoOneOneOneOne => exact w21111OK
  | singletons => exact w111111OK

#print axioms all_words_accept

end GaussianChains.Point22.Atlas
