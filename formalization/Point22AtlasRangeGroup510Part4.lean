import Point22AtlasRangeGroup510Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s16384_256 : Run get 16384 256 ⟨836467104,876935303⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨877140343,941530039⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨941830662,1031170426⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨1031571398,1147263355⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨1147770906,1291589611⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨1292211427,1466301863⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨1467047080,1673921405⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨1674800587,1917333147⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨1918358269,2199778377⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨2200962786,2524844713⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨2526203088,2896452653⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨2898000938,3318838111⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨3320593443,3796530315⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨3798510928,4334324487⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨4336549592,4937248716⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨4939738361,5610524532⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
