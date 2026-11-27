import BandVerifiedCacheCheck

/-! Small kernel reductions for profiling the exhaustive table verifier. -/
namespace GaussianChains.Band.Fast

set_option maxRecDepth 100000 in
theorem sample_page_pilot : validatePage 0 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem strip_node_pilot : runChecks (validateNode 0) 3 0 = true := by decide +kernel

end GaussianChains.Band.Fast
