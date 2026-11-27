import Point22AtlasRangeGroup220Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s16384_256 : Run get 16384 256 ⟨-377946,-366246⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨-395536,-377991⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨-418983,-395604⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨-448269,-419075⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨-483357,-448384⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨-524194,-483494⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨-570689,-524351⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨-622726,-570870⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨-680133,-622927⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨-742689,-680357⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨-810104,-742931⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨-882011,-810363⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨-957969,-882288⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨-1037432,-958261⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨-1119763,-1037738⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨-1204212,-1120078⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
