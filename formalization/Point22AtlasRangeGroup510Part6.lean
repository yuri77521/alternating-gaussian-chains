import Point22AtlasRangeGroup510Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s24576_256 : Run get 24576 256 ⟨29986055707,32503830877⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨32513930769,35145289402⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨35155823543,37894595057⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨37905536463,40744118246⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨40755434255,43684768276⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨43696420504,46705989380⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨46717933733,49795777777⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨49807964573,52940721036⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨52953095194,56126060524⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨56138561860,59335777442⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨59348341047,62552702385⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨62565259100,65758647969⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨65771124948,68934563516⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨68946884874,72060710354⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨72072797887,75116855718⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨75128629693,78082482818⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
