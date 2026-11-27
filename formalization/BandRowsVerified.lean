import BandRowsDecided
import BandVerifiedCacheCertified

namespace GaussianChains.Band

/-- The starting box is fixed by the support. The generated data supplies its
typed covering tree and a feasible trial. -/
theorem rowExcluded (s : Slab) (b : Fin s.count) (i : Fin 18) : RowExcluded s b i :=
  Material.allExcluded Fast.certifiedPacketCache s b i

#print axioms rowExcluded
end GaussianChains.Band
