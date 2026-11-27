import Point22AtlasWord21111Page8

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem w21111LLLROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRBox w21111LLLRTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRBox w21111LLLRLBox w21111LLLRRBox w21111LLLRTree
    (by decide +kernel) w21111LLLRLOK w21111LLLRROK

theorem w21111LLLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLBox w21111LLLTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLBox w21111LLLLBox w21111LLLRBox w21111LLLTree
    (by decide +kernel) w21111LLLLOK w21111LLLROK

theorem w21111LLRLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLRLBox w21111LLRLTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLRLBox w21111LLRLLBox w21111LLRLRBox w21111LLRLTree
    (by decide +kernel) w21111LLRLLOK w21111LLRLROK

theorem w21111LLROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLRBox w21111LLRTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLRBox w21111LLRLBox w21111LLRRBox w21111LLRTree
    (by decide +kernel) w21111LLRLOK w21111LLRROK

theorem w21111LLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLBox w21111LLTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLBox w21111LLLBox w21111LLRBox w21111LLTree
    (by decide +kernel) w21111LLLOK w21111LLROK

theorem w21111LROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LRBox w21111LRTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LRBox w21111LRLBox w21111LRRBox w21111LRTree
    (by decide +kernel) w21111LRLOK w21111LRROK

theorem w21111LOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LBox w21111LTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LBox w21111LLBox w21111LRBox w21111LTree
    (by decide +kernel) w21111LLOK w21111LROK

theorem w21111OK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111Box w21111Tree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111Box w21111LBox w21111RBox w21111Tree
    (by decide +kernel) w21111LOK w21111ROK

theorem word21111_accept : atlasAccept .twoOneOneOneOne = true := w21111OK


end GaussianChains.Point22.Atlas
