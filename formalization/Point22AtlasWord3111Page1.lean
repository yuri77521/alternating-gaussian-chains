import Point22AtlasWord3111Page0

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w3111LLRLLLBox := endpointsBox (0,0) (96,8048) (128,8080) (16064,24016) (0,0) (0,0)
def w3111LLRLLLTree := leftSubtree w3111LLRLLTree

def w3111LLRLLRBox := endpointsBox (0,0) (96,8048) (128,8080) (24016,31968) (0,0) (0,0)
def w3111LLRLLRTree := rightSubtree w3111LLRLLTree

theorem w3111LLRLLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLRLLLBox w3111LLRLLLTree = true := by
  decide +kernel

theorem w3111LLRLLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLRLLRBox w3111LLRLLRTree = true := by
  decide +kernel

theorem w3111LLRLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLRLLBox w3111LLRLLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLRLLBox w3111LLRLLLBox w3111LLRLLRBox w3111LLRLLTree
    (by decide +kernel) w3111LLRLLLOK w3111LLRLLROK


end GaussianChains.Point22.Atlas
