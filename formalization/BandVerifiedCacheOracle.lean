import BandExecutable

/-! Grid and range interfaces used by the three materialized Gaussian caches.
The spatial range already includes the local Lipschitz error. The slab-width
error is added once after clamping to the physical displacement interval. -/

namespace GaussianChains.Band.Fast

open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds
open GaussianChains.Strip

structure RawOracle where
  raw : Order → ℕ → Interval
  range : Order → ℕ → ℕ → Interval

structure Valid (s : Slab) (C : RawOracle) : Prop where
  raw_mem (j : Order) (p : ℕ) (hp : p ≤ 8192) :
    (C.raw j p).Mem ((deriv^[orderIndex j] (kernel (s.anchor:ℝ))) ((p:ℝ)/8192))
  range_cover (j : Order) {l p r : ℕ} (hl : l ≤ p) (hr : p ≤ r) (hr' : r ≤ 8192) :
    (C.range j l r).lo ≤ (paddedNode 8192 1000000000 (stripCap j) (C.raw j) p).lo ∧
    (paddedNode 8192 1000000000 (stripCap j) (C.raw j) p).hi ≤ (C.range j l r).hi

def RawOracle.query (C : RawOracle) (j : Order) (lo hi : ℚ) : Interval :=
  C.range j (nearest 8192 lo) (nearest 8192 hi)

def RawOracle.taylor (C : RawOracle) (x : ℚ) : ℚ :=
  taylorAt 8192 1000000000 (C.raw .value) (C.raw .first) x

def RawOracle.accurate (C : RawOracle) (x : ℚ) : Bool :=
  midpointOK 1000000000 (C.raw .value (nearest 8192 x)) &&
    midpointOK 1000000000 (C.raw .first (nearest 8192 x))

def oracle (s : Slab) (C : RawOracle) : Oracle := fun p I =>
  pad (C.query (imageOrder p) (max 0 I.lo) (min 1 I.hi)) (s.radius p)

def realTest (s : Slab) (C : RawOracle) (floor : Interval) (A : Support)
    (j : Fin 5) (B : Box 6) : Witness → Bool
  | .transfer r => testLeaf (oracle s C) floor A j B r
  | .centered c => valueTest (oracle s C) C.taylor
      (taylorBudget 8192 1000000000 20 + s.radius 0) C.accurate floor B c j

def checkRow (s : Slab) (C : RawOracle) (b : Fin s.count) (i : Fin 18) : Bool :=
  packetCheck s b i (realTest s C (s.floor b) (support i))

end GaussianChains.Band.Fast
