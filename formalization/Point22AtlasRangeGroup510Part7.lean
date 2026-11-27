import Point22AtlasRangeGroup510Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s28672_256 : Run get 28672 256 ⟨78093862823,80937014207⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨80947920046,83660045140⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨83670397759,86231583336⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨86241305765,88632291248⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨88641309549,90843726785⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨90851970986,92848578331⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨92855983325,94630889864⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨94637396261,96176272122⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨96181827046,97472095883⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨97476653686,98507663760⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨98511186644,99274357220⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨99276815758,99765756002⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨99767129554,99906837323⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨99907663471,99951069185⟩ :=
  of_check (by decide +kernel)

theorem s31936_32 : Run get 31936 32 ⟨99951620904,99966596187⟩ :=
  of_check (by decide +kernel)

theorem s31968_1 : Run get 31968 1 ⟨99967010574,99967010589⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
