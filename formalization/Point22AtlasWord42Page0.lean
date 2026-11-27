import Point22AtlasWordPartitions

/-! Generated evaluation shards. Regenerate with point22_atlas_word_proofs.py. -/
namespace GaussianChains.Point22.Atlas
open GaussianChains.Cert

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem w42OK : replay .fourTwo (wordBounds .fourTwo) w42Box w42Tree = true := by
  decide +kernel


end GaussianChains.Point22.Atlas
