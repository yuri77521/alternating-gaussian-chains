import Point22AtlasRangeGroup420Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s12288_256 : Run get 12288 256 ⟨-1936110,-1783795⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨-1783235,-1638852⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨-1638327,-1502790⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨-1502302,-1376356⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨-1375909,-1260150⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨-1259740,-1154632⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨-1154264,-1060154⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨-1059830,-976969⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨-976691,-905259⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨-905027,-845144⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨-844956,-796696⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨-796551,-759956⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨-759859,-734951⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨-734901,-721690⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨-721686,-719366⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨-730434,-720193⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
