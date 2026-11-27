import CertTree
import CertTreeTails

namespace GaussianChains.Point22.Atlas.Tables
open GaussianChains.Cert

structure Ticks where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def Ticks.decode (D : ℕ+) (v : Ticks) : Interval :=
  ⟨(v.lo:ℚ)/D,(v.hi:ℚ)/D⟩

end GaussianChains.Point22.Atlas.Tables
