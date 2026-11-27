import Point22AtlasWord111111Page11

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w111111LLRLRRLBox := endpointsBox (0,0) (32,4008) (8016,15968) (23952,31904) (23984,31936) (24016,31968)
def w111111LLRLRRLTree := leftSubtree w111111LLRLRRTree

def w111111LLRLRRRBox := endpointsBox (0,0) (4008,7984) (8016,15968) (23952,31904) (23984,31936) (24016,31968)
def w111111LLRLRRRTree := rightSubtree w111111LLRLRRTree

def w111111LLRLRRRLBox := endpointsBox (0,0) (4008,7984) (8016,11992) (23952,31904) (23984,31936) (24016,31968)
def w111111LLRLRRRLTree := leftSubtree w111111LLRLRRRTree

def w111111LLRLRRRRBox := endpointsBox (0,0) (4008,7984) (11992,15968) (23952,31904) (23984,31936) (24016,31968)
def w111111LLRLRRRRTree := rightSubtree w111111LLRLRRRTree

def w111111LLRLRRRRLBox := endpointsBox (0,0) (4008,7984) (11992,15968) (23952,27928) (23984,31936) (24016,31968)
def w111111LLRLRRRRLTree := leftSubtree w111111LLRLRRRRTree

def w111111LLRLRRRRRBox := endpointsBox (0,0) (4008,7984) (11992,15968) (27928,31904) (23984,31936) (24016,31968)
def w111111LLRLRRRRRTree := rightSubtree w111111LLRLRRRRTree

def w111111LLRLRRRRLLBox := endpointsBox (0,0) (4008,7984) (11992,15968) (23952,27928) (23984,27960) (24016,31968)
def w111111LLRLRRRRLLTree := leftSubtree w111111LLRLRRRRLTree

def w111111LLRLRRRRLRBox := endpointsBox (0,0) (4008,7984) (11992,15968) (23952,27928) (27960,31936) (24016,31968)
def w111111LLRLRRRRLRTree := rightSubtree w111111LLRLRRRRLTree

def w111111LLRLRRRRLLLBox := endpointsBox (0,0) (4008,7984) (11992,15968) (23952,27928) (23984,27960) (24016,27992)
def w111111LLRLRRRRLLLTree := leftSubtree w111111LLRLRRRRLLTree

def w111111LLRLRRRRLLRBox := endpointsBox (0,0) (4008,7984) (11992,15968) (23952,27928) (23984,27960) (27992,31968)
def w111111LLRLRRRRLLRTree := rightSubtree w111111LLRLRRRRLLTree

def w111111LLRLRRRRLLLLBox := endpointsBox (0,0) (4008,5996) (11992,15968) (23952,27928) (23984,27960) (24016,27992)
def w111111LLRLRRRRLLLLTree := leftSubtree w111111LLRLRRRRLLLTree

def w111111LLRLRRRRLLLRBox := endpointsBox (0,0) (5996,7984) (11992,15968) (23952,27928) (23984,27960) (24016,27992)
def w111111LLRLRRRRLLLRTree := rightSubtree w111111LLRLRRRRLLLTree

theorem w111111LLRLRRLOK : replay .singletons (wordBounds .singletons) w111111LLRLRRLBox w111111LLRLRRLTree = true := by
  decide +kernel

theorem w111111LLRLRRRLOK : replay .singletons (wordBounds .singletons) w111111LLRLRRRLBox w111111LLRLRRRLTree = true := by
  decide +kernel

theorem w111111LLRLRRRRLLLLOK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRLLLLBox w111111LLRLRRRRLLLLTree = true := by
  decide +kernel

theorem w111111LLRLRRRRLLLROK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRLLLRBox w111111LLRLRRRRLLLRTree = true := by
  decide +kernel

theorem w111111LLRLRRRRLLLOK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRLLLBox w111111LLRLRRRRLLLTree = true := by
  exact replay_join_checked .singletons w111111LLRLRRRRLLLBox w111111LLRLRRRRLLLLBox w111111LLRLRRRRLLLRBox w111111LLRLRRRRLLLTree
    (by decide +kernel) w111111LLRLRRRRLLLLOK w111111LLRLRRRRLLLROK

theorem w111111LLRLRRRRLLROK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRLLRBox w111111LLRLRRRRLLRTree = true := by
  decide +kernel

theorem w111111LLRLRRRRLLOK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRLLBox w111111LLRLRRRRLLTree = true := by
  exact replay_join_checked .singletons w111111LLRLRRRRLLBox w111111LLRLRRRRLLLBox w111111LLRLRRRRLLRBox w111111LLRLRRRRLLTree
    (by decide +kernel) w111111LLRLRRRRLLLOK w111111LLRLRRRRLLROK

theorem w111111LLRLRRRRLROK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRLRBox w111111LLRLRRRRLRTree = true := by
  decide +kernel

theorem w111111LLRLRRRRLOK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRLBox w111111LLRLRRRRLTree = true := by
  exact replay_join_checked .singletons w111111LLRLRRRRLBox w111111LLRLRRRRLLBox w111111LLRLRRRRLRBox w111111LLRLRRRRLTree
    (by decide +kernel) w111111LLRLRRRRLLOK w111111LLRLRRRRLROK

theorem w111111LLRLRRRRROK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRRBox w111111LLRLRRRRRTree = true := by
  decide +kernel

theorem w111111LLRLRRRROK : replay .singletons (wordBounds .singletons) w111111LLRLRRRRBox w111111LLRLRRRRTree = true := by
  exact replay_join_checked .singletons w111111LLRLRRRRBox w111111LLRLRRRRLBox w111111LLRLRRRRRBox w111111LLRLRRRRTree
    (by decide +kernel) w111111LLRLRRRRLOK w111111LLRLRRRRROK

theorem w111111LLRLRRROK : replay .singletons (wordBounds .singletons) w111111LLRLRRRBox w111111LLRLRRRTree = true := by
  exact replay_join_checked .singletons w111111LLRLRRRBox w111111LLRLRRRLBox w111111LLRLRRRRBox w111111LLRLRRRTree
    (by decide +kernel) w111111LLRLRRRLOK w111111LLRLRRRROK

theorem w111111LLRLRROK : replay .singletons (wordBounds .singletons) w111111LLRLRRBox w111111LLRLRRTree = true := by
  exact replay_join_checked .singletons w111111LLRLRRBox w111111LLRLRRLBox w111111LLRLRRRBox w111111LLRLRRTree
    (by decide +kernel) w111111LLRLRRLOK w111111LLRLRRROK


end GaussianChains.Point22.Atlas
