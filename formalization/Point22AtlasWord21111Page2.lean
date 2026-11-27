import Point22AtlasWord21111Page1

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w21111LLLRRLBox := endpointsBox (0,0) (8016,15968) (8048,16000) (8080,16032) (16064,24016) (0,0)
def w21111LLLRRLTree := leftSubtree w21111LLLRRTree

def w21111LLLRRRBox := endpointsBox (0,0) (8016,15968) (8048,16000) (8080,16032) (24016,31968) (0,0)
def w21111LLLRRRTree := rightSubtree w21111LLLRRTree

def w21111LLLRRLLBox := endpointsBox (0,0) (8016,11992) (8048,16000) (8080,16032) (16064,24016) (0,0)
def w21111LLLRRLLTree := leftSubtree w21111LLLRRLTree

def w21111LLLRRLRBox := endpointsBox (0,0) (11992,15968) (8048,16000) (8080,16032) (16064,24016) (0,0)
def w21111LLLRRLRTree := rightSubtree w21111LLLRRLTree

def w21111LLLRRLLLBox := endpointsBox (0,0) (8016,11992) (8048,12024) (8080,16032) (16064,24016) (0,0)
def w21111LLLRRLLLTree := leftSubtree w21111LLLRRLLTree

def w21111LLLRRLLRBox := endpointsBox (0,0) (8016,11992) (12024,16000) (8080,16032) (16064,24016) (0,0)
def w21111LLLRRLLRTree := rightSubtree w21111LLLRRLLTree

def w21111LLLRRLLLLBox := endpointsBox (0,0) (8016,11992) (8048,12024) (8080,12056) (16064,24016) (0,0)
def w21111LLLRRLLLLTree := leftSubtree w21111LLLRRLLLTree

def w21111LLLRRLLLRBox := endpointsBox (0,0) (8016,11992) (8048,12024) (12056,16032) (16064,24016) (0,0)
def w21111LLLRRLLLRTree := rightSubtree w21111LLLRRLLLTree

def w21111LLLRRLLLRLBox := endpointsBox (0,0) (8016,11992) (8048,12024) (12056,16032) (16064,20040) (0,0)
def w21111LLLRRLLLRLTree := leftSubtree w21111LLLRRLLLRTree

def w21111LLLRRLLLRRBox := endpointsBox (0,0) (8016,11992) (8048,12024) (12056,16032) (20040,24016) (0,0)
def w21111LLLRRLLLRRTree := rightSubtree w21111LLLRRLLLRTree

def w21111LLLRRLLRLBox := endpointsBox (0,0) (8016,11992) (12024,16000) (12056,16032) (16064,20040) (0,0)
def w21111LLLRRLLRLTree := leftSubtree w21111LLLRRLLRTree

def w21111LLLRRLLRRBox := endpointsBox (0,0) (8016,11992) (12024,16000) (12056,16032) (20040,24016) (0,0)
def w21111LLLRRLLRRTree := rightSubtree w21111LLLRRLLRTree

def w21111LLLRRRLBox := endpointsBox (0,0) (8016,11992) (8048,16000) (8080,16032) (24016,31968) (0,0)
def w21111LLLRRRLTree := leftSubtree w21111LLLRRRTree

def w21111LLLRRRRBox := endpointsBox (0,0) (11992,15968) (8048,16000) (8080,16032) (24016,31968) (0,0)
def w21111LLLRRRRTree := rightSubtree w21111LLLRRRTree

def w21111LLLRRRLLBox := endpointsBox (0,0) (8016,11992) (8048,12024) (8080,16032) (24016,31968) (0,0)
def w21111LLLRRRLLTree := leftSubtree w21111LLLRRRLTree

def w21111LLLRRRLRBox := endpointsBox (0,0) (8016,11992) (12024,16000) (8080,16032) (24016,31968) (0,0)
def w21111LLLRRRLRTree := rightSubtree w21111LLLRRRLTree

theorem w21111LLLRRLLLLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLLLBox w21111LLLRRLLLLTree = true := by
  decide +kernel

theorem w21111LLLRRLLLRLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLLRLBox w21111LLLRRLLLRLTree = true := by
  decide +kernel

theorem w21111LLLRRLLLRROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLLRRBox w21111LLLRRLLLRRTree = true := by
  decide +kernel

theorem w21111LLLRRLLLROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLLRBox w21111LLLRRLLLRTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRLLLRBox w21111LLLRRLLLRLBox w21111LLLRRLLLRRBox w21111LLLRRLLLRTree
    (by decide +kernel) w21111LLLRRLLLRLOK w21111LLLRRLLLRROK

theorem w21111LLLRRLLLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLLBox w21111LLLRRLLLTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRLLLBox w21111LLLRRLLLLBox w21111LLLRRLLLRBox w21111LLLRRLLLTree
    (by decide +kernel) w21111LLLRRLLLLOK w21111LLLRRLLLROK

theorem w21111LLLRRLLRLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLRLBox w21111LLLRRLLRLTree = true := by
  decide +kernel

theorem w21111LLLRRLLRROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLRRBox w21111LLLRRLLRRTree = true := by
  decide +kernel

theorem w21111LLLRRLLROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLRBox w21111LLLRRLLRTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRLLRBox w21111LLLRRLLRLBox w21111LLLRRLLRRBox w21111LLLRRLLRTree
    (by decide +kernel) w21111LLLRRLLRLOK w21111LLLRRLLRROK

theorem w21111LLLRRLLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLLBox w21111LLLRRLLTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRLLBox w21111LLLRRLLLBox w21111LLLRRLLRBox w21111LLLRRLLTree
    (by decide +kernel) w21111LLLRRLLLOK w21111LLLRRLLROK

theorem w21111LLLRRLROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLRBox w21111LLLRRLRTree = true := by
  decide +kernel

theorem w21111LLLRRLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRLBox w21111LLLRRLTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRLBox w21111LLLRRLLBox w21111LLLRRLRBox w21111LLLRRLTree
    (by decide +kernel) w21111LLLRRLLOK w21111LLLRRLROK

theorem w21111LLLRRRLLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRRLLBox w21111LLLRRRLLTree = true := by
  decide +kernel

theorem w21111LLLRRRLROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRRLRBox w21111LLLRRRLRTree = true := by
  decide +kernel

theorem w21111LLLRRRLOK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRRLBox w21111LLLRRRLTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRRLBox w21111LLLRRRLLBox w21111LLLRRRLRBox w21111LLLRRRLTree
    (by decide +kernel) w21111LLLRRRLLOK w21111LLLRRRLROK

theorem w21111LLLRRRROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRRRBox w21111LLLRRRRTree = true := by
  decide +kernel

theorem w21111LLLRRROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRRBox w21111LLLRRRTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRRBox w21111LLLRRRLBox w21111LLLRRRRBox w21111LLLRRRTree
    (by decide +kernel) w21111LLLRRRLOK w21111LLLRRRROK

theorem w21111LLLRROK : replay .twoOneOneOneOne (wordBounds .twoOneOneOneOne) w21111LLLRRBox w21111LLLRRTree = true := by
  exact replay_join_checked .twoOneOneOneOne w21111LLLRRBox w21111LLLRRLBox w21111LLLRRRBox w21111LLLRRTree
    (by decide +kernel) w21111LLLRRLOK w21111LLLRRROK


end GaussianChains.Point22.Atlas
