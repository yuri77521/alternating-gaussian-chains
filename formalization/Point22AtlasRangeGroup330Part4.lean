import Point22AtlasRangeGroup330Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s16384_256 : Run get 16384 256 ⟨844059947,890420870⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨890649370,961148028⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨961473142,1057231579⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨1057658436,1180172035⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨1180707235,1331843422⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨1332495014,1514490983⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨1515268465,1730727555⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨1731641842,1983528037⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨1984591452,2276221536⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨2277447761,2612480518⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨2613884561,2996306432⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨2997904545,3432011156⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨3433820756,3924193631⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨3926233215,4477711191⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨4480000192,5097644872⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨5100203528,5789258374⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
