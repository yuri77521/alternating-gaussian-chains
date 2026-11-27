import BandVerifiedCacheCheck

namespace GaussianChains.Band.Fast

/-- The only finite checks required to validate one materialized anchor. -/
structure Checked (a : Fin 3) : Prop where
  init : stateAt a 0 = Fixed.init a
  recurrence : runChecks (validatePage a) 10 0 = true
  grid : runChecks (validateNode a) 13 0 = true
  last : validateNode a 8192 = true

end GaussianChains.Band.Fast
