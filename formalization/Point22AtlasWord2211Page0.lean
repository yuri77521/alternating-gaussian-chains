import Point22AtlasWord2121Page0

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def w2211LBox := endpointsBox (0,0) (64,15968) (128,31936) (160,31968) (0,0) (0,0)
def w2211LTree := leftSubtree w2211Tree

def w2211RBox := endpointsBox (0,0) (15968,31872) (128,31936) (160,31968) (0,0) (0,0)
def w2211RTree := rightSubtree w2211Tree

def w2211LLBox := endpointsBox (0,0) (64,15968) (128,16032) (160,31968) (0,0) (0,0)
def w2211LLTree := leftSubtree w2211LTree

def w2211LRBox := endpointsBox (0,0) (64,15968) (16032,31936) (160,31968) (0,0) (0,0)
def w2211LRTree := rightSubtree w2211LTree

theorem w2211LLOK : replay .twoTwoOneOne (wordBounds .twoTwoOneOne) w2211LLBox w2211LLTree = true := by
  decide +kernel

theorem w2211LROK : replay .twoTwoOneOne (wordBounds .twoTwoOneOne) w2211LRBox w2211LRTree = true := by
  decide +kernel

theorem w2211LOK : replay .twoTwoOneOne (wordBounds .twoTwoOneOne) w2211LBox w2211LTree = true := by
  exact replay_join_checked .twoTwoOneOne w2211LBox w2211LLBox w2211LRBox w2211LTree
    (by decide +kernel) w2211LLOK w2211LROK

theorem w2211ROK : replay .twoTwoOneOne (wordBounds .twoTwoOneOne) w2211RBox w2211RTree = true := by
  decide +kernel

theorem w2211OK : replay .twoTwoOneOne (wordBounds .twoTwoOneOne) w2211Box w2211Tree = true := by
  exact replay_join_checked .twoTwoOneOne w2211Box w2211LBox w2211RBox w2211Tree
    (by decide +kernel) w2211LOK w2211ROK


end GaussianChains.Point22.Atlas
