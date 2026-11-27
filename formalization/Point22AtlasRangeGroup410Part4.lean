import Point22AtlasRangeGroup410Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s16384_256 : Run get 16384 256 ⟨7588806,13478604⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨13502052,19608095⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨19632575,26048331⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨26074208,32892945⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨32920585,40235184⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨40264949,48167635⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨48199887,56781853⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨56816945,66167852⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨66206133,76413472⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨76455279,87603593⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨87649253,99819200⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨99869018,113136293⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨113190554,127624637⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨127683601,143346383⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨143410274,160354535⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨160423541,178691314⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
