import Point22AtlasRangeGroup220Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s28672_256 : Run get 28672 256 ⟨1817686,2134499⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨2135718,2445165⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨2446347,2744651⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨2745782,3029203⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨3030269,3295173⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨3296158,3539083⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨3539977,3757691⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨3758479,3948049⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨3948721,4107557⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨4108106,4234020⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨4234434,4325677⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨4325951,4381249⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨4381381,4395240⟩ :=
  of_check (by decide +kernel)

theorem s31872_1 : Run get 31872 1 ⟨4395301,4395313⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨4395301,4398760⟩ :=
  of_check (by decide +kernel)

theorem s31936_1 : Run get 31936 1 ⟨4398784,4398796⟩ :=
  of_check (by decide +kernel)

theorem s31872_32 : Run get 31872 32 ⟨4395301,4397289⟩ :=
  of_check (by decide +kernel)

theorem s31904_1 : Run get 31904 1 ⟨4397332,4397344⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
