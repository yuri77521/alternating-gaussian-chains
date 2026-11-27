import Point22AtlasWord51Page0

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem w222OK : replay .twoTwoTwo (wordBounds .twoTwoTwo) w222Box w222Tree = true := by
  decide +kernel


end GaussianChains.Point22.Atlas
