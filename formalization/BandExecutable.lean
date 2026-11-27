import BandSchedule
import BandTaylorBase
import CertTreeStripCache

namespace GaussianChains.Band
open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds
open GaussianChains.Strip Interval

def Slab.radius (s : Slab) (p : ℕ) : ℚ :=
  let costs : Fin 3 → ℕ := match s with
    | .narrow => ![42761,539098,6806367]
    | .lower => ![1156027,14580271,184224460]
    | .upper => ![1309984,16545550,209498225]
  (costs (Fin.ofNat 3 p) : ℚ)/10^9

def imageOrder : ℕ → ImageBounds.Order
  | 0 => .value | 1 => .first | _ => .second

def Slab.oracle (s : Slab) (C : StripCache) : Oracle := fun p I =>
  pad (C.query (imageOrder p) (max 0 I.lo) (min 1 I.hi)) (s.radius p)

def realTest (s : Slab) (C : StripCache) (floor : Interval) (A : Support)
    (j : Fin 5) (B : Box 6) : Witness → Bool
  | .transfer r => testLeaf (s.oracle C) floor A j B r
  | .centered c => valueTest (s.oracle C) C.taylor
      (taylorBudget 8192 1000000000 20 + s.radius 0) C.accurate floor B c j

def checkRow (s : Slab) (C : StripCache) (b : Fin s.count) (i : Fin 18) : Bool :=
  packetCheck s b i (realTest s C (s.floor b) (support i))

end GaussianChains.Band
