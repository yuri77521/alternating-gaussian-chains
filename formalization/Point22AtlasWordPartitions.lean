import Point22AtlasWordJoin
import Point22AtlasAcceptance

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev wordBounds (w : Word) := boundsFrom checkedLookup internalTicks witnessTicks w

def w42Box := rootBox .fourTwo
def w42Tree := tree .fourTwo

def w51Box := rootBox .fiveOne
def w51Tree := tree .fiveOne

def w222Box := rootBox .twoTwoTwo
def w222Tree := tree .twoTwoTwo

def w321Box := rootBox .threeTwoOne
def w321Tree := tree .threeTwoOne

def w411Box := rootBox .fourOneOne
def w411Tree := tree .fourOneOne

def w2121Box := rootBox .twoOneTwoOne
def w2121Tree := tree .twoOneTwoOne

def w2211Box := rootBox .twoTwoOneOne
def w2211Tree := tree .twoTwoOneOne

def w3111Box := rootBox .threeOneOneOne
def w3111Tree := tree .threeOneOneOne

def w3111LBox := endpointsBox (0,0) (96,16000) (128,31936) (160,31968) (0,0) (0,0)
def w3111LTree := leftSubtree w3111Tree

def w3111RBox := endpointsBox (0,0) (16000,31904) (128,31936) (160,31968) (0,0) (0,0)
def w3111RTree := rightSubtree w3111Tree

def w3111LLBox := endpointsBox (0,0) (96,16000) (128,16032) (160,31968) (0,0) (0,0)
def w3111LLTree := leftSubtree w3111LTree

def w3111LRBox := endpointsBox (0,0) (96,16000) (16032,31936) (160,31968) (0,0) (0,0)
def w3111LRTree := rightSubtree w3111LTree

def w3111LLLBox := endpointsBox (0,0) (96,16000) (128,16032) (160,16064) (0,0) (0,0)
def w3111LLLTree := leftSubtree w3111LLTree

def w3111LLRBox := endpointsBox (0,0) (96,16000) (128,16032) (16064,31968) (0,0) (0,0)
def w3111LLRTree := rightSubtree w3111LLTree

def w3111LLRLBox := endpointsBox (0,0) (96,8048) (128,16032) (16064,31968) (0,0) (0,0)
def w3111LLRLTree := leftSubtree w3111LLRTree

def w3111LLRRBox := endpointsBox (0,0) (8048,16000) (128,16032) (16064,31968) (0,0) (0,0)
def w3111LLRRTree := rightSubtree w3111LLRTree

def w3111LLRLLBox := endpointsBox (0,0) (96,8048) (128,8080) (16064,31968) (0,0) (0,0)
def w3111LLRLLTree := leftSubtree w3111LLRLTree

def w3111LLRLRBox := endpointsBox (0,0) (96,8048) (8080,16032) (16064,31968) (0,0) (0,0)
def w3111LLRLRTree := rightSubtree w3111LLRLTree

def w3111LLRLRLBox := endpointsBox (0,0) (96,8048) (8080,16032) (16064,24016) (0,0) (0,0)
def w3111LLRLRLTree := leftSubtree w3111LLRLRTree

def w3111LLRLRRBox := endpointsBox (0,0) (96,8048) (8080,16032) (24016,31968) (0,0) (0,0)
def w3111LLRLRRTree := rightSubtree w3111LLRLRTree

def w3111LRLBox := endpointsBox (0,0) (96,8048) (16032,31936) (16064,31968) (0,0) (0,0)
def w3111LRLTree := leftSubtree w3111LRTree

def w3111LRRBox := endpointsBox (0,0) (8048,16000) (16032,31936) (16064,31968) (0,0) (0,0)
def w3111LRRTree := rightSubtree w3111LRTree

def w21111Box := rootBox .twoOneOneOneOne
def w21111Tree := tree .twoOneOneOneOne

def w21111LBox := endpointsBox (0,0) (64,15968) (96,31904) (128,31936) (160,31968) (0,0)
def w21111LTree := leftSubtree w21111Tree

def w21111RBox := endpointsBox (0,0) (15968,31872) (96,31904) (128,31936) (160,31968) (0,0)
def w21111RTree := rightSubtree w21111Tree

def w21111LLBox := endpointsBox (0,0) (64,15968) (96,16000) (128,31936) (160,31968) (0,0)
def w21111LLTree := leftSubtree w21111LTree

def w21111LRBox := endpointsBox (0,0) (64,15968) (16000,31904) (128,31936) (160,31968) (0,0)
def w21111LRTree := rightSubtree w21111LTree

def w21111LLLBox := endpointsBox (0,0) (64,15968) (96,16000) (128,16032) (160,31968) (0,0)
def w21111LLLTree := leftSubtree w21111LLTree

def w21111LLRBox := endpointsBox (0,0) (64,15968) (96,16000) (16032,31936) (160,31968) (0,0)
def w21111LLRTree := rightSubtree w21111LLTree

def w21111LLLLBox := endpointsBox (0,0) (64,15968) (96,16000) (128,16032) (160,16064) (0,0)
def w21111LLLLTree := leftSubtree w21111LLLTree

def w21111LLLRBox := endpointsBox (0,0) (64,15968) (96,16000) (128,16032) (16064,31968) (0,0)
def w21111LLLRTree := rightSubtree w21111LLLTree

def w21111LLLRLBox := endpointsBox (0,0) (64,8016) (96,16000) (128,16032) (16064,31968) (0,0)
def w21111LLLRLTree := leftSubtree w21111LLLRTree

def w21111LLLRRBox := endpointsBox (0,0) (8016,15968) (96,16000) (128,16032) (16064,31968) (0,0)
def w21111LLLRRTree := rightSubtree w21111LLLRTree

def w21111LLRLBox := endpointsBox (0,0) (64,8016) (96,16000) (16032,31936) (16064,31968) (0,0)
def w21111LLRLTree := leftSubtree w21111LLRTree

def w21111LLRRBox := endpointsBox (0,0) (8016,15968) (96,16000) (16032,31936) (16064,31968) (0,0)
def w21111LLRRTree := rightSubtree w21111LLRTree

def w21111LLRLLBox := endpointsBox (0,0) (64,8016) (96,8048) (16032,31936) (16064,31968) (0,0)
def w21111LLRLLTree := leftSubtree w21111LLRLTree

def w21111LLRLRBox := endpointsBox (0,0) (64,8016) (8048,16000) (16032,31936) (16064,31968) (0,0)
def w21111LLRLRTree := rightSubtree w21111LLRLTree

def w21111LRLBox := endpointsBox (0,0) (64,8016) (16000,31904) (16032,31936) (16064,31968) (0,0)
def w21111LRLTree := leftSubtree w21111LRTree

def w21111LRRBox := endpointsBox (0,0) (8016,15968) (16000,31904) (16032,31936) (16064,31968) (0,0)
def w21111LRRTree := rightSubtree w21111LRTree

def w111111Box := rootBox .singletons
def w111111Tree := tree .singletons

def w111111LBox := endpointsBox (0,0) (32,15936) (64,31872) (96,31904) (128,31936) (160,31968)
def w111111LTree := leftSubtree w111111Tree

def w111111RBox := endpointsBox (0,0) (15936,31840) (64,31872) (96,31904) (128,31936) (160,31968)
def w111111RTree := rightSubtree w111111Tree

def w111111LLBox := endpointsBox (0,0) (32,15936) (64,15968) (96,31904) (128,31936) (160,31968)
def w111111LLTree := leftSubtree w111111LTree

def w111111LRBox := endpointsBox (0,0) (32,15936) (15968,31872) (96,31904) (128,31936) (160,31968)
def w111111LRTree := rightSubtree w111111LTree

def w111111LLLBox := endpointsBox (0,0) (32,15936) (64,15968) (96,16000) (128,31936) (160,31968)
def w111111LLLTree := leftSubtree w111111LLTree

def w111111LLRBox := endpointsBox (0,0) (32,15936) (64,15968) (16000,31904) (128,31936) (160,31968)
def w111111LLRTree := rightSubtree w111111LLTree

def w111111LLLLBox := endpointsBox (0,0) (32,15936) (64,15968) (96,16000) (128,16032) (160,31968)
def w111111LLLLTree := leftSubtree w111111LLLTree

def w111111LLLRBox := endpointsBox (0,0) (32,15936) (64,15968) (96,16000) (16032,31936) (160,31968)
def w111111LLLRTree := rightSubtree w111111LLLTree

def w111111LLLLLBox := endpointsBox (0,0) (32,15936) (64,15968) (96,16000) (128,16032) (160,16064)
def w111111LLLLLTree := leftSubtree w111111LLLLTree

def w111111LLLLRBox := endpointsBox (0,0) (32,15936) (64,15968) (96,16000) (128,16032) (16064,31968)
def w111111LLLLRTree := rightSubtree w111111LLLLTree

def w111111LLLLRLBox := endpointsBox (0,0) (32,7984) (64,15968) (96,16000) (128,16032) (16064,31968)
def w111111LLLLRLTree := leftSubtree w111111LLLLRTree

def w111111LLLLRRBox := endpointsBox (0,0) (7984,15936) (64,15968) (96,16000) (128,16032) (16064,31968)
def w111111LLLLRRTree := rightSubtree w111111LLLLRTree

def w111111LLLLRLLBox := endpointsBox (0,0) (32,7984) (64,8016) (96,16000) (128,16032) (16064,31968)
def w111111LLLLRLLTree := leftSubtree w111111LLLLRLTree

def w111111LLLLRLRBox := endpointsBox (0,0) (32,7984) (8016,15968) (96,16000) (128,16032) (16064,31968)
def w111111LLLLRLRTree := rightSubtree w111111LLLLRLTree

def w111111LLLLRLLLBox := endpointsBox (0,0) (32,7984) (64,8016) (96,8048) (128,16032) (16064,31968)
def w111111LLLLRLLLTree := leftSubtree w111111LLLLRLLTree

def w111111LLLLRLLRBox := endpointsBox (0,0) (32,7984) (64,8016) (8048,16000) (128,16032) (16064,31968)
def w111111LLLLRLLRTree := rightSubtree w111111LLLLRLLTree

def w111111LLLRLBox := endpointsBox (0,0) (32,7984) (64,15968) (96,16000) (16032,31936) (16064,31968)
def w111111LLLRLTree := leftSubtree w111111LLLRTree

def w111111LLLRRBox := endpointsBox (0,0) (7984,15936) (64,15968) (96,16000) (16032,31936) (16064,31968)
def w111111LLLRRTree := rightSubtree w111111LLLRTree

def w111111LLLRLLBox := endpointsBox (0,0) (32,7984) (64,8016) (96,16000) (16032,31936) (16064,31968)
def w111111LLLRLLTree := leftSubtree w111111LLLRLTree

def w111111LLLRLRBox := endpointsBox (0,0) (32,7984) (8016,15968) (96,16000) (16032,31936) (16064,31968)
def w111111LLLRLRTree := rightSubtree w111111LLLRLTree

def w111111LLRLBox := endpointsBox (0,0) (32,7984) (64,15968) (16000,31904) (16032,31936) (16064,31968)
def w111111LLRLTree := leftSubtree w111111LLRTree

def w111111LLRRBox := endpointsBox (0,0) (7984,15936) (64,15968) (16000,31904) (16032,31936) (16064,31968)
def w111111LLRRTree := rightSubtree w111111LLRTree

def w111111LLRLLBox := endpointsBox (0,0) (32,7984) (64,8016) (16000,31904) (16032,31936) (16064,31968)
def w111111LLRLLTree := leftSubtree w111111LLRLTree

def w111111LLRLRBox := endpointsBox (0,0) (32,7984) (8016,15968) (16000,31904) (16032,31936) (16064,31968)
def w111111LLRLRTree := rightSubtree w111111LLRLTree

def w111111LLRLRLBox := endpointsBox (0,0) (32,7984) (8016,15968) (16000,23952) (16032,31936) (16064,31968)
def w111111LLRLRLTree := leftSubtree w111111LLRLRTree

def w111111LLRLRRBox := endpointsBox (0,0) (32,7984) (8016,15968) (23952,31904) (16032,31936) (16064,31968)
def w111111LLRLRRTree := rightSubtree w111111LLRLRTree

def w111111LLRLRLLBox := endpointsBox (0,0) (32,7984) (8016,15968) (16000,23952) (16032,23984) (16064,31968)
def w111111LLRLRLLTree := leftSubtree w111111LLRLRLTree

def w111111LLRLRLRBox := endpointsBox (0,0) (32,7984) (8016,15968) (16000,23952) (23984,31936) (16064,31968)
def w111111LLRLRLRTree := rightSubtree w111111LLRLRLTree

def w111111LLRLRLLLBox := endpointsBox (0,0) (32,7984) (8016,15968) (16000,23952) (16032,23984) (16064,24016)
def w111111LLRLRLLLTree := leftSubtree w111111LLRLRLLTree

def w111111LLRLRLLRBox := endpointsBox (0,0) (32,7984) (8016,15968) (16000,23952) (16032,23984) (24016,31968)
def w111111LLRLRLLRTree := rightSubtree w111111LLRLRLLTree

def w111111LLRRLBox := endpointsBox (0,0) (7984,15936) (8016,15968) (16000,23952) (16032,31936) (16064,31968)
def w111111LLRRLTree := leftSubtree w111111LLRRTree

def w111111LLRRRBox := endpointsBox (0,0) (7984,15936) (8016,15968) (23952,31904) (16032,31936) (16064,31968)
def w111111LLRRRTree := rightSubtree w111111LLRRTree

def w111111LRLBox := endpointsBox (0,0) (32,7984) (15968,31872) (16000,31904) (16032,31936) (16064,31968)
def w111111LRLTree := leftSubtree w111111LRTree

def w111111LRRBox := endpointsBox (0,0) (7984,15936) (15968,31872) (16000,31904) (16032,31936) (16064,31968)
def w111111LRRTree := rightSubtree w111111LRTree


end GaussianChains.Point22.Atlas
