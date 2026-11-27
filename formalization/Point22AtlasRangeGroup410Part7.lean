import Point22AtlasRangeGroup410Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s28672_256 : Run get 28672 256 ⟨696168170,726716984⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨660454090,696038440⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨619821707,660304842⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨574468746,619653595⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨524652525,574282660⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨470687935,524449585⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨412944388,470469482⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨351841766,412711964⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨287845420,351597105⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨221460325,287590423⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨153224459,221197032⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨83701552,152955026⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨48638765,83428222⟩ :=
  of_check (by decide +kernel)

theorem s31872_64 : Run get 31872 64 ⟨31064249,48364349⟩ :=
  of_check (by decide +kernel)

theorem s31936_32 : Run get 31936 32 ⟨22270261,30789505⟩ :=
  of_check (by decide +kernel)

theorem s31968_1 : Run get 31968 1 ⟨21995396,21995408⟩ :=
  of_check (by decide +kernel)

theorem s31936_1 : Run get 31936 1 ⟨30789493,30789505⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
