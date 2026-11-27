import Point22AtlasRangeGroup420Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s16384_256 : Run get 16384 256 ⟨-752411,-730473⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨-786124,-752496⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨-831556,-786254⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨-888671,-831734⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨-957401,-888894⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨-1037643,-957670⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨-1129230,-1037954⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨-1231931,-1129586⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨-1345422,-1232330⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨-1469271,-1345864⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨-1602917,-1469749⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨-1745647,-1603431⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨-1896597,-1746198⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨-2054703,-1897177⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨-2218713,-2055311⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨-2387158,-2219342⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
