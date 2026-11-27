import Point22AtlasRangeGroup110Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s28672_256 : Run get 28672 256 ⟨78824054707,81637293325⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨81648071908,84325235857⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨84335441635,86856746881⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨86866303511,89212679038⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨89221513444,91374840198⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨91382883497,93326226581⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨93333414979,95051244966⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨95057520594,96535919916⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨96541231608,97768082183⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨97772386171,98737534749⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨98740795259,99436193313⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨99438383066,99858198546⟩ :=
  of_check (by decide +kernel)

theorem s31744_64 : Run get 31744 64 ⟨99859299134,99920004924⟩ :=
  of_check (by decide +kernel)

theorem s31808_32 : Run get 31808 32 ⟨99920831411,99944325914⟩ :=
  of_check (by decide +kernel)

theorem s31840_1 : Run get 31840 1 ⟨99945015178,99945015181⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨99859299134,99964254300⟩ :=
  of_check (by decide +kernel)

theorem s31872_32 : Run get 31872 32 ⟨99964806250,99979787452⟩ :=
  of_check (by decide +kernel)

theorem s31904_1 : Run get 31904 1 ⟨99980202015,99980202018⟩ :=
  of_check (by decide +kernel)

theorem s31872_1 : Run get 31872 1 ⟨99964806250,99964806253⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
