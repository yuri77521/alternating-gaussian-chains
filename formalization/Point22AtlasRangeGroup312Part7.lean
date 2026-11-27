import Point22AtlasRangeGroup312Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf312
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .second

theorem s28672_256 : Run get 28672 256 ⟨-2094964015938,-1777561236698⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨-2406706721676,-2096197678257⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨-2707742708875,-2407905940926⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨-2994310759253,-2708892688057⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨-3262747088691,-2995396954454⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨-3509550607704,-3263755465082⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨-3731446640001,-3510467892406⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨-3925447613719,-3732260566013⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨-4088909282716,-3926147149147⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨-4219581120097,-4089484839803⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨-4315649650920,-4220024738988⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨-4375773652559,-4315955153622⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨-4392073095743,-4375936763276⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨-4396751806823,-4392164025418⟩ :=
  of_check (by decide +kernel)

theorem s31936_32 : Run get 31936 32 ⟨-4398221275146,-4396806510142⟩ :=
  of_check (by decide +kernel)

theorem s31968_1 : Run get 31968 1 ⟨-4398257845255,-4398257845246⟩ :=
  of_check (by decide +kernel)

theorem s31872_32 : Run get 31872 32 ⟨-4394702263435,-4392164025418⟩ :=
  of_check (by decide +kernel)

theorem s31904_1 : Run get 31904 1 ⟨-4394775087947,-4394775087938⟩ :=
  of_check (by decide +kernel)

theorem s29980_4 : Run get 29980 4 ⟨-3294850161025,-3291855048362⟩ :=
  of_check (by decide +kernel)

theorem s29984_32 : Run get 29984 32 ⟨-3326608310652,-3295847858482⟩ :=
  of_check (by decide +kernel)

theorem s30016_64 : Run get 30016 64 ⟨-3389063652926,-3327595123236⟩ :=
  of_check (by decide +kernel)

theorem s30080_128 : Run get 30080 128 ⟨-3509550607704,-3390028085286⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf312
