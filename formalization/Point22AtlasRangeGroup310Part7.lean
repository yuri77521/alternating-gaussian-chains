import Point22AtlasRangeGroup310Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf310
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .value

theorem s28672_256 : Run get 28672 256 ⟨78460676148,81289189471⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨81300032921,83994989578⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨84005269984,86546817567⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨86556458257,88925427211⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨88934354664,91112497712⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨91120642486,93090867834⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨93098165466,94844759634⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨94851151481,96359987715⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨96365421745,97624150130⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨97628581625,98626797347⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨98630189513,99359576050⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨99361900527,99816345012⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨99817582272,99939933313⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨99940622480,99975390172⟩ :=
  of_check (by decide +kernel)

theorem s31936_32 : Run get 31936 32 ⟨99975804674,99986524570⟩ :=
  of_check (by decide +kernel)

theorem s31968_1 : Run get 31968 1 ⟨99986801649,99986801658⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf310
