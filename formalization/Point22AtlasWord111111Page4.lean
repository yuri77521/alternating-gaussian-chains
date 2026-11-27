import Point22AtlasWord111111Page3

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w111111LLLLRRLBox := endpointsBox (0,0) (7984,15936) (8016,15968) (8048,16000) (8080,16032) (16064,24016)
def w111111LLLLRRLTree := leftSubtree w111111LLLLRRTree

def w111111LLLLRRRBox := endpointsBox (0,0) (7984,15936) (8016,15968) (8048,16000) (8080,16032) (24016,31968)
def w111111LLLLRRRTree := rightSubtree w111111LLLLRRTree

def w111111LLLLRRLLBox := endpointsBox (0,0) (7984,11960) (8016,15968) (8048,16000) (8080,16032) (16064,24016)
def w111111LLLLRRLLTree := leftSubtree w111111LLLLRRLTree

def w111111LLLLRRLRBox := endpointsBox (0,0) (11960,15936) (8016,15968) (8048,16000) (8080,16032) (16064,24016)
def w111111LLLLRRLRTree := rightSubtree w111111LLLLRRLTree

def w111111LLLLRRLLLBox := endpointsBox (0,0) (7984,11960) (8016,11992) (8048,16000) (8080,16032) (16064,24016)
def w111111LLLLRRLLLTree := leftSubtree w111111LLLLRRLLTree

def w111111LLLLRRLLRBox := endpointsBox (0,0) (7984,11960) (11992,15968) (8048,16000) (8080,16032) (16064,24016)
def w111111LLLLRRLLRTree := rightSubtree w111111LLLLRRLLTree

def w111111LLLLRRLLLLBox := endpointsBox (0,0) (7984,11960) (8016,11992) (8048,12024) (8080,16032) (16064,24016)
def w111111LLLLRRLLLLTree := leftSubtree w111111LLLLRRLLLTree

def w111111LLLLRRLLLRBox := endpointsBox (0,0) (7984,11960) (8016,11992) (12024,16000) (8080,16032) (16064,24016)
def w111111LLLLRRLLLRTree := rightSubtree w111111LLLLRRLLLTree

def w111111LLLLRRLLLRLBox := endpointsBox (0,0) (7984,11960) (8016,11992) (12024,16000) (12056,16032) (16064,20040)
def w111111LLLLRRLLLRLTree := leftSubtree w111111LLLLRRLLLRTree

def w111111LLLLRRLLLRRBox := endpointsBox (0,0) (7984,11960) (8016,11992) (12024,16000) (12056,16032) (20040,24016)
def w111111LLLLRRLLLRRTree := rightSubtree w111111LLLLRRLLLRTree

def w111111LLLLRRLLRLBox := endpointsBox (0,0) (7984,11960) (11992,15968) (12024,16000) (12056,16032) (16064,20040)
def w111111LLLLRRLLRLTree := leftSubtree w111111LLLLRRLLRTree

def w111111LLLLRRLLRRBox := endpointsBox (0,0) (7984,11960) (11992,15968) (12024,16000) (12056,16032) (20040,24016)
def w111111LLLLRRLLRRTree := rightSubtree w111111LLLLRRLLRTree

def w111111LLLLRRRLBox := endpointsBox (0,0) (7984,11960) (8016,15968) (8048,16000) (8080,16032) (24016,31968)
def w111111LLLLRRRLTree := leftSubtree w111111LLLLRRRTree

def w111111LLLLRRRRBox := endpointsBox (0,0) (11960,15936) (8016,15968) (8048,16000) (8080,16032) (24016,31968)
def w111111LLLLRRRRTree := rightSubtree w111111LLLLRRRTree

def w111111LLLLRRRLLBox := endpointsBox (0,0) (7984,11960) (8016,11992) (8048,16000) (8080,16032) (24016,31968)
def w111111LLLLRRRLLTree := leftSubtree w111111LLLLRRRLTree

def w111111LLLLRRRLRBox := endpointsBox (0,0) (7984,11960) (11992,15968) (8048,16000) (8080,16032) (24016,31968)
def w111111LLLLRRRLRTree := rightSubtree w111111LLLLRRRLTree

theorem w111111LLLLRRLLLLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLLLBox w111111LLLLRRLLLLTree = true := by
  decide +kernel

theorem w111111LLLLRRLLLRLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLLRLBox w111111LLLLRRLLLRLTree = true := by
  decide +kernel

theorem w111111LLLLRRLLLRROK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLLRRBox w111111LLLLRRLLLRRTree = true := by
  decide +kernel

theorem w111111LLLLRRLLLROK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLLRBox w111111LLLLRRLLLRTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRLLLRBox w111111LLLLRRLLLRLBox w111111LLLLRRLLLRRBox w111111LLLLRRLLLRTree
    (by decide +kernel) w111111LLLLRRLLLRLOK w111111LLLLRRLLLRROK

theorem w111111LLLLRRLLLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLLBox w111111LLLLRRLLLTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRLLLBox w111111LLLLRRLLLLBox w111111LLLLRRLLLRBox w111111LLLLRRLLLTree
    (by decide +kernel) w111111LLLLRRLLLLOK w111111LLLLRRLLLROK

theorem w111111LLLLRRLLRLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLRLBox w111111LLLLRRLLRLTree = true := by
  decide +kernel

theorem w111111LLLLRRLLRROK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLRRBox w111111LLLLRRLLRRTree = true := by
  decide +kernel

theorem w111111LLLLRRLLROK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLRBox w111111LLLLRRLLRTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRLLRBox w111111LLLLRRLLRLBox w111111LLLLRRLLRRBox w111111LLLLRRLLRTree
    (by decide +kernel) w111111LLLLRRLLRLOK w111111LLLLRRLLRROK

theorem w111111LLLLRRLLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRLLBox w111111LLLLRRLLTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRLLBox w111111LLLLRRLLLBox w111111LLLLRRLLRBox w111111LLLLRRLLTree
    (by decide +kernel) w111111LLLLRRLLLOK w111111LLLLRRLLROK

theorem w111111LLLLRRLROK : replay .singletons (wordBounds .singletons) w111111LLLLRRLRBox w111111LLLLRRLRTree = true := by
  decide +kernel

theorem w111111LLLLRRLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRLBox w111111LLLLRRLTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRLBox w111111LLLLRRLLBox w111111LLLLRRLRBox w111111LLLLRRLTree
    (by decide +kernel) w111111LLLLRRLLOK w111111LLLLRRLROK

theorem w111111LLLLRRRLLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRRLLBox w111111LLLLRRRLLTree = true := by
  decide +kernel

theorem w111111LLLLRRRLROK : replay .singletons (wordBounds .singletons) w111111LLLLRRRLRBox w111111LLLLRRRLRTree = true := by
  decide +kernel

theorem w111111LLLLRRRLOK : replay .singletons (wordBounds .singletons) w111111LLLLRRRLBox w111111LLLLRRRLTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRRLBox w111111LLLLRRRLLBox w111111LLLLRRRLRBox w111111LLLLRRRLTree
    (by decide +kernel) w111111LLLLRRRLLOK w111111LLLLRRRLROK

theorem w111111LLLLRRRROK : replay .singletons (wordBounds .singletons) w111111LLLLRRRRBox w111111LLLLRRRRTree = true := by
  decide +kernel

theorem w111111LLLLRRROK : replay .singletons (wordBounds .singletons) w111111LLLLRRRBox w111111LLLLRRRTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRRBox w111111LLLLRRRLBox w111111LLLLRRRRBox w111111LLLLRRRTree
    (by decide +kernel) w111111LLLLRRRLOK w111111LLLLRRRROK

theorem w111111LLLLRROK : replay .singletons (wordBounds .singletons) w111111LLLLRRBox w111111LLLLRRTree = true := by
  exact replay_join_checked .singletons w111111LLLLRRBox w111111LLLLRRLBox w111111LLLLRRRBox w111111LLLLRRTree
    (by decide +kernel) w111111LLLLRRLOK w111111LLLLRRROK


end GaussianChains.Point22.Atlas
