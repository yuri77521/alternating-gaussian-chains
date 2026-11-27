import Point22AtlasWord3111Page6

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w3111RLBox := endpointsBox (0,0) (16000,23952) (16032,31936) (16064,31968) (0,0) (0,0)
def w3111RLTree := leftSubtree w3111RTree

def w3111RRBox := endpointsBox (0,0) (23952,31904) (16032,31936) (16064,31968) (0,0) (0,0)
def w3111RRTree := rightSubtree w3111RTree

def w3111RLLBox := endpointsBox (0,0) (16000,23952) (16032,23984) (16064,31968) (0,0) (0,0)
def w3111RLLTree := leftSubtree w3111RLTree

def w3111RLRBox := endpointsBox (0,0) (16000,23952) (23984,31936) (16064,31968) (0,0) (0,0)
def w3111RLRTree := rightSubtree w3111RLTree

def w3111RLLLBox := endpointsBox (0,0) (16000,23952) (16032,23984) (16064,24016) (0,0) (0,0)
def w3111RLLLTree := leftSubtree w3111RLLTree

def w3111RLLRBox := endpointsBox (0,0) (16000,23952) (16032,23984) (24016,31968) (0,0) (0,0)
def w3111RLLRTree := rightSubtree w3111RLLTree

def w3111RLRLBox := endpointsBox (0,0) (16000,19976) (23984,31936) (24016,31968) (0,0) (0,0)
def w3111RLRLTree := leftSubtree w3111RLRTree

def w3111RLRRBox := endpointsBox (0,0) (19976,23952) (23984,31936) (24016,31968) (0,0) (0,0)
def w3111RLRRTree := rightSubtree w3111RLRTree

def w3111RRLBox := endpointsBox (0,0) (23952,27928) (23984,31936) (24016,31968) (0,0) (0,0)
def w3111RRLTree := leftSubtree w3111RRTree

def w3111RRRBox := endpointsBox (0,0) (27928,31904) (23984,31936) (24016,31968) (0,0) (0,0)
def w3111RRRTree := rightSubtree w3111RRTree

def w3111RRLLBox := endpointsBox (0,0) (23952,27928) (23984,27960) (24016,31968) (0,0) (0,0)
def w3111RRLLTree := leftSubtree w3111RRLTree

def w3111RRLRBox := endpointsBox (0,0) (23952,27928) (27960,31936) (24016,31968) (0,0) (0,0)
def w3111RRLRTree := rightSubtree w3111RRLTree

theorem w3111RLLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RLLLBox w3111RLLLTree = true := by
  decide +kernel

theorem w3111RLLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RLLRBox w3111RLLRTree = true := by
  decide +kernel

theorem w3111RLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RLLBox w3111RLLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111RLLBox w3111RLLLBox w3111RLLRBox w3111RLLTree
    (by decide +kernel) w3111RLLLOK w3111RLLROK

theorem w3111RLRLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RLRLBox w3111RLRLTree = true := by
  decide +kernel

theorem w3111RLRROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RLRRBox w3111RLRRTree = true := by
  decide +kernel

theorem w3111RLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RLRBox w3111RLRTree = true := by
  exact replay_join_checked .threeOneOneOne w3111RLRBox w3111RLRLBox w3111RLRRBox w3111RLRTree
    (by decide +kernel) w3111RLRLOK w3111RLRROK

theorem w3111RLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RLBox w3111RLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111RLBox w3111RLLBox w3111RLRBox w3111RLTree
    (by decide +kernel) w3111RLLOK w3111RLROK

theorem w3111RRLLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RRLLBox w3111RRLLTree = true := by
  decide +kernel

theorem w3111RRLROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RRLRBox w3111RRLRTree = true := by
  decide +kernel

theorem w3111RRLOK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RRLBox w3111RRLTree = true := by
  exact replay_join_checked .threeOneOneOne w3111RRLBox w3111RRLLBox w3111RRLRBox w3111RRLTree
    (by decide +kernel) w3111RRLLOK w3111RRLROK

theorem w3111RRROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RRRBox w3111RRRTree = true := by
  decide +kernel

theorem w3111RROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RRBox w3111RRTree = true := by
  exact replay_join_checked .threeOneOneOne w3111RRBox w3111RRLBox w3111RRRBox w3111RRTree
    (by decide +kernel) w3111RRLOK w3111RRROK

theorem w3111ROK : replay .threeOneOneOne (wordBounds .threeOneOneOne) w3111RBox w3111RTree = true := by
  exact replay_join_checked .threeOneOneOne w3111RBox w3111RLBox w3111RRBox w3111RTree
    (by decide +kernel) w3111RLOK w3111RROK


end GaussianChains.Point22.Atlas
