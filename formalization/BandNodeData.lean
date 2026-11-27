import BandContractWitness
import BandSchedule
import BandVerifiedCacheInstance

namespace GaussianChains.Band.Material
open GaussianChains.Cert

/-- Pack the six nonnegative integer coordinates into one literal. Integer
subexpressions are forced at individual table accesses, independent of tree depth. -/
def ticks (w : ℕ) (i : Fin 6) : ℤ := ((w >>> (14*i.val)) % 16384 : ℕ)

def box (l h : ℕ) : ChamberBox := ⟨ticks l, ticks h⟩

def stage (a b l h : ℕ) : ChamberPass := ⟨ticks a, ticks b, box l h⟩

def center (w : ℕ) : Witness := .centered (fun i => chamberTick (ticks w i))

def floorId (s : Slab) (n : ℕ) : Fin s.count :=
  ⟨n % s.count, Nat.mod_lt _ (by cases s <;> decide +kernel)⟩

end GaussianChains.Band.Material
