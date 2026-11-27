import Point22AtlasRangeGroup120Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s16384_256 : Run get 16384 256 ⟨-7492548,-4525369⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨-10591374,-7504382⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨-13857290,-10603770⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨-17337076,-13870431⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨-21077287,-17351144⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨-25124112,-21092463⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨-29523160,-25140574⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨-34319204,-29541087⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨-39555837,-34338768⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨-45275063,-39577207⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨-51516809,-45298397⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨-58318360,-51542258⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨-65713725,-58346066⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨-73732912,-65743812⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨-82401163,-73765489⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨-91738113,-82436318⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
