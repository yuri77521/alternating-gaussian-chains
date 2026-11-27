import Point22AtlasWord111111Page16

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w111111RLBox := endpointsBox (0,0) (15936,23888) (15968,31872) (16000,31904) (16032,31936) (16064,31968)
def w111111RLTree := leftSubtree w111111RTree

def w111111RRBox := endpointsBox (0,0) (23888,31840) (15968,31872) (16000,31904) (16032,31936) (16064,31968)
def w111111RRTree := rightSubtree w111111RTree

def w111111RLLBox := endpointsBox (0,0) (15936,23888) (15968,23920) (16000,31904) (16032,31936) (16064,31968)
def w111111RLLTree := leftSubtree w111111RLTree

def w111111RLRBox := endpointsBox (0,0) (15936,23888) (23920,31872) (16000,31904) (16032,31936) (16064,31968)
def w111111RLRTree := rightSubtree w111111RLTree

def w111111RLLLBox := endpointsBox (0,0) (15936,23888) (15968,23920) (16000,23952) (16032,31936) (16064,31968)
def w111111RLLLTree := leftSubtree w111111RLLTree

def w111111RLLRBox := endpointsBox (0,0) (15936,23888) (15968,23920) (23952,31904) (16032,31936) (16064,31968)
def w111111RLLRTree := rightSubtree w111111RLLTree

theorem w111111RLLLOK : replay .singletons (wordBounds .singletons) w111111RLLLBox w111111RLLLTree = true := by
  decide +kernel

theorem w111111RLLROK : replay .singletons (wordBounds .singletons) w111111RLLRBox w111111RLLRTree = true := by
  decide +kernel

theorem w111111RLLOK : replay .singletons (wordBounds .singletons) w111111RLLBox w111111RLLTree = true := by
  exact replay_join_checked .singletons w111111RLLBox w111111RLLLBox w111111RLLRBox w111111RLLTree
    (by decide +kernel) w111111RLLLOK w111111RLLROK

theorem w111111RLROK : replay .singletons (wordBounds .singletons) w111111RLRBox w111111RLRTree = true := by
  decide +kernel

theorem w111111RLOK : replay .singletons (wordBounds .singletons) w111111RLBox w111111RLTree = true := by
  exact replay_join_checked .singletons w111111RLBox w111111RLLBox w111111RLRBox w111111RLTree
    (by decide +kernel) w111111RLLOK w111111RLROK

theorem w111111RROK : replay .singletons (wordBounds .singletons) w111111RRBox w111111RRTree = true := by
  decide +kernel

theorem w111111ROK : replay .singletons (wordBounds .singletons) w111111RBox w111111RTree = true := by
  exact replay_join_checked .singletons w111111RBox w111111RLBox w111111RRBox w111111RTree
    (by decide +kernel) w111111RLOK w111111RROK


end GaussianChains.Point22.Atlas
