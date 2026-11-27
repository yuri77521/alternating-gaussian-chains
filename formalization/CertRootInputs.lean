import CertRootFinite

namespace GaussianChains.Root22

/-- Published rational endpoints of the reflection-symmetric root at width 22. -/
def lowerRoot : ℚ := 249999032167246504146498709394 / 10^30
def upperRoot : ℚ := 249999032167246504146498709395 / 10^30

/-- Absolute error allowance for the omitted images at each kernel evaluation. -/
def tailRadius : ℚ := 1 / 10^50

end GaussianChains.Root22
