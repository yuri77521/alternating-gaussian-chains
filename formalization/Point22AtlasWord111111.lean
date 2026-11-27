import Point22AtlasWord111111Page17

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem w111111LLLLRLLOK : replay .singletons (wordBounds .singletons) w111111LLLLRLLBox w111111LLLLRLLTree = true := by
  exact replay_join_checked .singletons w111111LLLLRLLBox w111111LLLLRLLLBox w111111LLLLRLLRBox w111111LLLLRLLTree
    (by decide +kernel) w111111LLLLRLLLOK w111111LLLLRLLROK

theorem w111111LLLLRLOK : replay .singletons (wordBounds .singletons) w111111LLLLRLBox w111111LLLLRLTree = true := by
  exact replay_join_checked .singletons w111111LLLLRLBox w111111LLLLRLLBox w111111LLLLRLRBox w111111LLLLRLTree
    (by decide +kernel) w111111LLLLRLLOK w111111LLLLRLROK

theorem w111111LLLLROK : replay .singletons (wordBounds .singletons) w111111LLLLRBox w111111LLLLRTree = true := by
  exact replay_join_checked .singletons w111111LLLLRBox w111111LLLLRLBox w111111LLLLRRBox w111111LLLLRTree
    (by decide +kernel) w111111LLLLRLOK w111111LLLLRROK

theorem w111111LLLLOK : replay .singletons (wordBounds .singletons) w111111LLLLBox w111111LLLLTree = true := by
  exact replay_join_checked .singletons w111111LLLLBox w111111LLLLLBox w111111LLLLRBox w111111LLLLTree
    (by decide +kernel) w111111LLLLLOK w111111LLLLROK

theorem w111111LLLRLOK : replay .singletons (wordBounds .singletons) w111111LLLRLBox w111111LLLRLTree = true := by
  exact replay_join_checked .singletons w111111LLLRLBox w111111LLLRLLBox w111111LLLRLRBox w111111LLLRLTree
    (by decide +kernel) w111111LLLRLLOK w111111LLLRLROK

theorem w111111LLLROK : replay .singletons (wordBounds .singletons) w111111LLLRBox w111111LLLRTree = true := by
  exact replay_join_checked .singletons w111111LLLRBox w111111LLLRLBox w111111LLLRRBox w111111LLLRTree
    (by decide +kernel) w111111LLLRLOK w111111LLLRROK

theorem w111111LLLOK : replay .singletons (wordBounds .singletons) w111111LLLBox w111111LLLTree = true := by
  exact replay_join_checked .singletons w111111LLLBox w111111LLLLBox w111111LLLRBox w111111LLLTree
    (by decide +kernel) w111111LLLLOK w111111LLLROK

theorem w111111LLRLRLLOK : replay .singletons (wordBounds .singletons) w111111LLRLRLLBox w111111LLRLRLLTree = true := by
  exact replay_join_checked .singletons w111111LLRLRLLBox w111111LLRLRLLLBox w111111LLRLRLLRBox w111111LLRLRLLTree
    (by decide +kernel) w111111LLRLRLLLOK w111111LLRLRLLROK

theorem w111111LLRLRLOK : replay .singletons (wordBounds .singletons) w111111LLRLRLBox w111111LLRLRLTree = true := by
  exact replay_join_checked .singletons w111111LLRLRLBox w111111LLRLRLLBox w111111LLRLRLRBox w111111LLRLRLTree
    (by decide +kernel) w111111LLRLRLLOK w111111LLRLRLROK

theorem w111111LLRLROK : replay .singletons (wordBounds .singletons) w111111LLRLRBox w111111LLRLRTree = true := by
  exact replay_join_checked .singletons w111111LLRLRBox w111111LLRLRLBox w111111LLRLRRBox w111111LLRLRTree
    (by decide +kernel) w111111LLRLRLOK w111111LLRLRROK

theorem w111111LLRLOK : replay .singletons (wordBounds .singletons) w111111LLRLBox w111111LLRLTree = true := by
  exact replay_join_checked .singletons w111111LLRLBox w111111LLRLLBox w111111LLRLRBox w111111LLRLTree
    (by decide +kernel) w111111LLRLLOK w111111LLRLROK

theorem w111111LLRROK : replay .singletons (wordBounds .singletons) w111111LLRRBox w111111LLRRTree = true := by
  exact replay_join_checked .singletons w111111LLRRBox w111111LLRRLBox w111111LLRRRBox w111111LLRRTree
    (by decide +kernel) w111111LLRRLOK w111111LLRRROK

theorem w111111LLROK : replay .singletons (wordBounds .singletons) w111111LLRBox w111111LLRTree = true := by
  exact replay_join_checked .singletons w111111LLRBox w111111LLRLBox w111111LLRRBox w111111LLRTree
    (by decide +kernel) w111111LLRLOK w111111LLRROK

theorem w111111LLOK : replay .singletons (wordBounds .singletons) w111111LLBox w111111LLTree = true := by
  exact replay_join_checked .singletons w111111LLBox w111111LLLBox w111111LLRBox w111111LLTree
    (by decide +kernel) w111111LLLOK w111111LLROK

theorem w111111LROK : replay .singletons (wordBounds .singletons) w111111LRBox w111111LRTree = true := by
  exact replay_join_checked .singletons w111111LRBox w111111LRLBox w111111LRRBox w111111LRTree
    (by decide +kernel) w111111LRLOK w111111LRROK

theorem w111111LOK : replay .singletons (wordBounds .singletons) w111111LBox w111111LTree = true := by
  exact replay_join_checked .singletons w111111LBox w111111LLBox w111111LRBox w111111LTree
    (by decide +kernel) w111111LLOK w111111LROK

theorem w111111OK : replay .singletons (wordBounds .singletons) w111111Box w111111Tree = true := by
  exact replay_join_checked .singletons w111111Box w111111LBox w111111RBox w111111Tree
    (by decide +kernel) w111111LOK w111111ROK

theorem word111111_accept : atlasAccept .singletons = true := w111111OK


end GaussianChains.Point22.Atlas
