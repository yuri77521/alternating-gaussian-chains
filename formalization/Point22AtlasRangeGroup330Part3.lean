import Point22AtlasRangeGroup330Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s12288_256 : Run get 12288 256 ⟨3435631243,3926233242⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨2999503474,3433820783⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨2615289357,2997904572⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨2278674684,2613884588⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨1985655501,2277447788⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨1732556712,1984591479⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨1516046482,1731641869⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨1333147109,1515268492⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨1181242904,1332495041⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨1058085732,1180707262⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨961798665,1057658463⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨890878266,961473169⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨844195885,890649397⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨820998371,844059974⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨818073652,820953214⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨820953187,843924394⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
