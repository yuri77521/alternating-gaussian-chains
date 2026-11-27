import Point22AtlasRangeGroup330Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s24576_256 : Run get 24576 256 ⟨30605206843,33151959390⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨33162170411,35821118019⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨35831757158,38596375006⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨38607413870,41469737252⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨41481141747,44431747349⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨44443477661,47471484729⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨47483495350,50576588161⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨50588828035,53733300828⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨53745713561,56926538630⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨56939062814,60139982126⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨60152551731,63356191939⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨63368736820,66556747022⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨66569193499,69722404684⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨69734676209,72833280766⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨72845298666,75869047891⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨75880732164,78809149173⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
