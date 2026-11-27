import Point22AtlasRangeGroup320Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s12288_256 : Run get 12288 256 ⟨58383068,65753579⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨51576473,58355365⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨45329911,51551024⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨39606132,45306578⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨34365231,39584762⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨29565230,34345670⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨25162552,29547307⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨21112441,25146094⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨17369290,21097269⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨13886921,17355227⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨10618783,13873787⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨7518103,10606396⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨4537976,7506276⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨1631447,4526527⟩ :=
  of_check (by decide +kernel)

theorem s15872_128 : Run get 15872 128 ⟨191101,1620194⟩ :=
  of_check (by decide +kernel)

theorem s16000_1 : Run get 16000 1 ⟨179858,179876⟩ :=
  of_check (by decide +kernel)

theorem s16000_128 : Run get 16000 128 ⟨-1248465,179876⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨-4148755,-1259707⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
