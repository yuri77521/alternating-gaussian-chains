import Point22AtlasRangeGroup330Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s28672_256 : Run get 28672 256 ⟨78820419367,81633024465⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨81643800564,84320345724⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨84330549090,86851257836⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨86860812156,89206620948⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨89215453175,91368250223⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨91376291501,93319148836⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨93326335401,95043730050⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨95050004053,96528024324⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨96533334623,97759867607⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨97764170454,98729067279⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨98732326912,99427542549⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨99429731699,99849436649⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨99850536921,99955464425⟩ :=
  of_check (by decide +kernel)

theorem s31872_32 : Run get 31872 32 ⟨99956016205,99970993476⟩ :=
  of_check (by decide +kernel)

theorem s31904_1 : Run get 31904 1 ⟨99971407906,99971407933⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
