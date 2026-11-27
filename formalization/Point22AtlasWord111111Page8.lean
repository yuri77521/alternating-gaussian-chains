import Point22AtlasWord111111Page7

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w111111LLRLLLBox := endpointsBox (0,0) (32,7984) (64,8016) (16000,23952) (16032,31936) (16064,31968)
def w111111LLRLLLTree := leftSubtree w111111LLRLLTree

def w111111LLRLLRBox := endpointsBox (0,0) (32,7984) (64,8016) (23952,31904) (16032,31936) (16064,31968)
def w111111LLRLLRTree := rightSubtree w111111LLRLLTree

def w111111LLRLLLLBox := endpointsBox (0,0) (32,7984) (64,8016) (16000,23952) (16032,23984) (16064,31968)
def w111111LLRLLLLTree := leftSubtree w111111LLRLLLTree

def w111111LLRLLLRBox := endpointsBox (0,0) (32,7984) (64,8016) (16000,23952) (23984,31936) (16064,31968)
def w111111LLRLLLRTree := rightSubtree w111111LLRLLLTree

def w111111LLRLLLLLBox := endpointsBox (0,0) (32,7984) (64,8016) (16000,23952) (16032,23984) (16064,24016)
def w111111LLRLLLLLTree := leftSubtree w111111LLRLLLLTree

def w111111LLRLLLLRBox := endpointsBox (0,0) (32,7984) (64,8016) (16000,23952) (16032,23984) (24016,31968)
def w111111LLRLLLLRTree := rightSubtree w111111LLRLLLLTree

def w111111LLRLLLLLLBox := endpointsBox (0,0) (32,4008) (64,8016) (16000,23952) (16032,23984) (16064,24016)
def w111111LLRLLLLLLTree := leftSubtree w111111LLRLLLLLTree

def w111111LLRLLLLLRBox := endpointsBox (0,0) (4008,7984) (64,8016) (16000,23952) (16032,23984) (16064,24016)
def w111111LLRLLLLLRTree := rightSubtree w111111LLRLLLLLTree

def w111111LLRLLLLRLBox := endpointsBox (0,0) (32,4008) (64,8016) (16000,23952) (16032,23984) (24016,31968)
def w111111LLRLLLLRLTree := leftSubtree w111111LLRLLLLRTree

def w111111LLRLLLLRRBox := endpointsBox (0,0) (4008,7984) (64,8016) (16000,23952) (16032,23984) (24016,31968)
def w111111LLRLLLLRRTree := rightSubtree w111111LLRLLLLRTree

def w111111LLRLLLLRLLBox := endpointsBox (0,0) (32,4008) (64,4040) (16000,23952) (16032,23984) (24016,31968)
def w111111LLRLLLLRLLTree := leftSubtree w111111LLRLLLLRLTree

def w111111LLRLLLLRLRBox := endpointsBox (0,0) (32,4008) (4040,8016) (16000,23952) (16032,23984) (24016,31968)
def w111111LLRLLLLRLRTree := rightSubtree w111111LLRLLLLRLTree

def w111111LLRLLLRLBox := endpointsBox (0,0) (32,4008) (64,8016) (16000,23952) (23984,31936) (24016,31968)
def w111111LLRLLLRLTree := leftSubtree w111111LLRLLLRTree

def w111111LLRLLLRRBox := endpointsBox (0,0) (4008,7984) (64,8016) (16000,23952) (23984,31936) (24016,31968)
def w111111LLRLLLRRTree := rightSubtree w111111LLRLLLRTree

def w111111LLRLLLRLLBox := endpointsBox (0,0) (32,4008) (64,4040) (16000,23952) (23984,31936) (24016,31968)
def w111111LLRLLLRLLTree := leftSubtree w111111LLRLLLRLTree

def w111111LLRLLLRLRBox := endpointsBox (0,0) (32,4008) (4040,8016) (16000,23952) (23984,31936) (24016,31968)
def w111111LLRLLLRLRTree := rightSubtree w111111LLRLLLRLTree

theorem w111111LLRLLLLLLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLLLLBox w111111LLRLLLLLLTree = true := by
  decide +kernel

theorem w111111LLRLLLLLROK : replay .singletons (wordBounds .singletons) w111111LLRLLLLLRBox w111111LLRLLLLLRTree = true := by
  decide +kernel

theorem w111111LLRLLLLLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLLLBox w111111LLRLLLLLTree = true := by
  exact replay_join_checked .singletons w111111LLRLLLLLBox w111111LLRLLLLLLBox w111111LLRLLLLLRBox w111111LLRLLLLLTree
    (by decide +kernel) w111111LLRLLLLLLOK w111111LLRLLLLLROK

theorem w111111LLRLLLLRLLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLLRLLBox w111111LLRLLLLRLLTree = true := by
  decide +kernel

theorem w111111LLRLLLLRLROK : replay .singletons (wordBounds .singletons) w111111LLRLLLLRLRBox w111111LLRLLLLRLRTree = true := by
  decide +kernel

theorem w111111LLRLLLLRLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLLRLBox w111111LLRLLLLRLTree = true := by
  exact replay_join_checked .singletons w111111LLRLLLLRLBox w111111LLRLLLLRLLBox w111111LLRLLLLRLRBox w111111LLRLLLLRLTree
    (by decide +kernel) w111111LLRLLLLRLLOK w111111LLRLLLLRLROK

theorem w111111LLRLLLLRROK : replay .singletons (wordBounds .singletons) w111111LLRLLLLRRBox w111111LLRLLLLRRTree = true := by
  decide +kernel

theorem w111111LLRLLLLROK : replay .singletons (wordBounds .singletons) w111111LLRLLLLRBox w111111LLRLLLLRTree = true := by
  exact replay_join_checked .singletons w111111LLRLLLLRBox w111111LLRLLLLRLBox w111111LLRLLLLRRBox w111111LLRLLLLRTree
    (by decide +kernel) w111111LLRLLLLRLOK w111111LLRLLLLRROK

theorem w111111LLRLLLLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLLBox w111111LLRLLLLTree = true := by
  exact replay_join_checked .singletons w111111LLRLLLLBox w111111LLRLLLLLBox w111111LLRLLLLRBox w111111LLRLLLLTree
    (by decide +kernel) w111111LLRLLLLLOK w111111LLRLLLLROK

theorem w111111LLRLLLRLLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLRLLBox w111111LLRLLLRLLTree = true := by
  decide +kernel

theorem w111111LLRLLLRLROK : replay .singletons (wordBounds .singletons) w111111LLRLLLRLRBox w111111LLRLLLRLRTree = true := by
  decide +kernel

theorem w111111LLRLLLRLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLRLBox w111111LLRLLLRLTree = true := by
  exact replay_join_checked .singletons w111111LLRLLLRLBox w111111LLRLLLRLLBox w111111LLRLLLRLRBox w111111LLRLLLRLTree
    (by decide +kernel) w111111LLRLLLRLLOK w111111LLRLLLRLROK

theorem w111111LLRLLLRROK : replay .singletons (wordBounds .singletons) w111111LLRLLLRRBox w111111LLRLLLRRTree = true := by
  decide +kernel

theorem w111111LLRLLLROK : replay .singletons (wordBounds .singletons) w111111LLRLLLRBox w111111LLRLLLRTree = true := by
  exact replay_join_checked .singletons w111111LLRLLLRBox w111111LLRLLLRLBox w111111LLRLLLRRBox w111111LLRLLLRTree
    (by decide +kernel) w111111LLRLLLRLOK w111111LLRLLLRROK

theorem w111111LLRLLLOK : replay .singletons (wordBounds .singletons) w111111LLRLLLBox w111111LLRLLLTree = true := by
  exact replay_join_checked .singletons w111111LLRLLLBox w111111LLRLLLLBox w111111LLRLLLRBox w111111LLRLLLTree
    (by decide +kernel) w111111LLRLLLLOK w111111LLRLLLROK

theorem w111111LLRLLROK : replay .singletons (wordBounds .singletons) w111111LLRLLRBox w111111LLRLLRTree = true := by
  decide +kernel

theorem w111111LLRLLOK : replay .singletons (wordBounds .singletons) w111111LLRLLBox w111111LLRLLTree = true := by
  exact replay_join_checked .singletons w111111LLRLLBox w111111LLRLLLBox w111111LLRLLRBox w111111LLRLLTree
    (by decide +kernel) w111111LLRLLLOK w111111LLRLLROK


end GaussianChains.Point22.Atlas
