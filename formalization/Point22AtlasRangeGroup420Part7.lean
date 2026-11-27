import Point22AtlasRangeGroup420Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s28672_256 : Run get 28672 256 ⟨3555152,4190030⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨4192474,4813564⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨4815940,5415686⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨5417963,5988871⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨5991019,6525789⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨6527781,7019438⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨7021251,7463268⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨7464872,7851305⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨7852680,8178257⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨8179386,8439625⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨8440489,8631781⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨8632365,8752040⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨8752339,8784641⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨8784799,8794000⟩ :=
  of_check (by decide +kernel)

theorem s31936_1 : Run get 31936 1 ⟨8794085,8794109⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
