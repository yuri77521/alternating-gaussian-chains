import Point22AtlasWordPartitions

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w3111LLLLBox := endpointsBox (0,0) (96,8048) (128,16032) (160,16064) (0,0) (0,0)
def w3111LLLLTree := leftSubtree w3111LLLTree

def w3111LLLRBox := endpointsBox (0,0) (8048,16000) (128,16032) (160,16064) (0,0) (0,0)
def w3111LLLRTree := rightSubtree w3111LLLTree

def w3111LLLLLBox := endpointsBox (0,0) (96,8048) (128,8080) (160,16064) (0,0) (0,0)
def w3111LLLLLTree := leftSubtree w3111LLLLTree

def w3111LLLLRBox := endpointsBox (0,0) (96,8048) (8080,16032) (160,16064) (0,0) (0,0)
def w3111LLLLRTree := rightSubtree w3111LLLLTree

def w3111LLLLLLBox := endpointsBox (0,0) (96,8048) (128,8080) (160,8112) (0,0) (0,0)
def w3111LLLLLLTree := leftSubtree w3111LLLLLTree

def w3111LLLLLRBox := endpointsBox (0,0) (96,8048) (128,8080) (8112,16064) (0,0) (0,0)
def w3111LLLLLRTree := rightSubtree w3111LLLLLTree

def w3111LLLLLRLBox := endpointsBox (0,0) (96,4072) (128,8080) (8112,16064) (0,0) (0,0)
def w3111LLLLLRLTree := leftSubtree w3111LLLLLRTree

def w3111LLLLLRRBox := endpointsBox (0,0) (4072,8048) (128,8080) (8112,16064) (0,0) (0,0)
def w3111LLLLLRRTree := rightSubtree w3111LLLLLRTree

theorem w3111LLLLLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLLLLBox w3111LLLLLLTree = true := by
  decide +kernel

theorem w3111LLLLLRLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLLLRLBox w3111LLLLLRLTree = true := by
  decide +kernel

theorem w3111LLLLLRROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLLLRRBox w3111LLLLLRRTree = true := by
  decide +kernel

theorem w3111LLLLLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLLLRBox w3111LLLLLRTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLLLLRBox w3111LLLLLRLBox w3111LLLLLRRBox w3111LLLLLRTree
    (by decide +kernel) w3111LLLLLRLOK w3111LLLLLRROK

theorem w3111LLLLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLLLBox w3111LLLLLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLLLLBox w3111LLLLLLBox w3111LLLLLRBox w3111LLLLLTree
    (by decide +kernel) w3111LLLLLLOK w3111LLLLLROK

theorem w3111LLLLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLLRBox w3111LLLLRTree = true := by
  decide +kernel

theorem w3111LLLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLLBox w3111LLLLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLLLBox w3111LLLLLBox w3111LLLLRBox w3111LLLLTree
    (by decide +kernel) w3111LLLLLOK w3111LLLLROK

theorem w3111LLLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLRBox w3111LLLRTree = true := by
  decide +kernel

theorem w3111LLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111LLLBox w3111LLLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111LLLBox w3111LLLLBox w3111LLLRBox w3111LLLTree
    (by decide +kernel) w3111LLLLOK w3111LLLROK


end GaussianChains.Point22.Atlas
