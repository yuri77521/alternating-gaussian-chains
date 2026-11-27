import Point22AtlasWord3111Page7

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem w3111LLRLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLRLRBox w3111LLRLRTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLRLRBox w3111LLRLRLBox w3111LLRLRRBox w3111LLRLRTree
    (by decide +kernel) w3111LLRLRLOK w3111LLRLRROK

theorem w3111LLRLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLRLBox w3111LLRLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLRLBox w3111LLRLLBox w3111LLRLRBox w3111LLRLTree
    (by decide +kernel) w3111LLRLLOK w3111LLRLROK

theorem w3111LLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLRBox w3111LLRTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLRBox w3111LLRLBox w3111LLRRBox w3111LLRTree
    (by decide +kernel) w3111LLRLOK w3111LLRROK

theorem w3111LLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLBox w3111LLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLBox w3111LLLBox w3111LLRBox w3111LLTree
    (by decide +kernel) w3111LLLOK w3111LLROK

theorem w3111LROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LRBox w3111LRTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LRBox w3111LRLBox w3111LRRBox w3111LRTree
    (by decide +kernel) w3111LRLOK w3111LRROK

theorem w3111LOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LBox w3111LTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LBox w3111LLBox w3111LRBox w3111LTree
    (by decide +kernel) w3111LLOK w3111LROK

theorem w3111OK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111Box w3111Tree = true := by
  exact replay_join_checked .threeOneOneOne w3111Box w3111LBox w3111RBox w3111Tree
    (by decide +kernel) w3111LOK w3111ROK

theorem word3111_accept : atlasAccept .threeOneOneOne = true := w3111OK


end GaussianChains.Point22.Atlas
