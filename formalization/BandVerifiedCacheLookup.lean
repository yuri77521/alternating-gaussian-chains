import BandVerifiedCacheData0
import BandVerifiedCacheData1
import BandVerifiedCacheData2
import BandVerifiedCacheRangeDefs
import CertTreeStripOracle

namespace GaussianChains.Band.Fast
open GaussianChains.Cert GaussianChains.Cert.Tables GaussianChains.ImageBounds

def rawTicks (a : Fin 3) (j : Order) (p : ℕ) : ℤ × ℤ :=
  unpackRaw <| match a.val, j with
    | 0, .value => Anchor0.raw0 p | 0, .first => Anchor0.raw1 p | 0, .second => Anchor0.raw2 p
    | 1, .value => Anchor1.raw0 p | 1, .first => Anchor1.raw1 p | 1, .second => Anchor1.raw2 p
    | _, .value => Anchor2.raw0 p | _, .first => Anchor2.raw1 p | _, .second => Anchor2.raw2 p

def turning (a : Fin 3) : Order → ℕ × ℕ
  | .first => match a.val with
    | 0 => (1921,6271) | 1 => (1907,6285) | _ => (1876,6316)
  | _ => (4096,4096)

def tickBox (lo hi : ℤ) : Interval := ⟨(lo:ℚ)/1000000000, (hi:ℚ)/1000000000⟩

def rawBox (a : Fin 3) (j : Order) (p : ℕ) : Interval :=
  let v := rawTicks a j p
  tickBox v.1 v.2

def paddingTicks : Order → ℤ
  | .value => 244141 | .first => 1220704 | .second => 9155274

/-- Both ends and the at-most-two clamped turning points suffice for the
exact closed integer range. The spatial (Lipschitz) padding is common to
every grid node at a given derivative order. -/
def lookupBox (a : Fin 3) (j : Order) (l r : ℕ) : Interval :=
  let k := turning a j
  let lo := (range (fun p => (rawTicks a j p).1) k.1 k.2 l r).1
  let hi := (range (fun p => (rawTicks a j p).2) k.1 k.2 l r).2
  tickBox (lo - paddingTicks j) (hi + paddingTicks j)

end GaussianChains.Band.Fast
