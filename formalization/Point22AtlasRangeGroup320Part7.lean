import Point22AtlasRangeGroup320Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s28672_256 : Run get 28672 256 ⟨-361560873,-345969355⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨-345903269,-327801114⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨-327725304,-307184663⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨-307099472,-284222624⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨-284128511,-259047313⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨-258944853,-231819664⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨-231709536,-202727641⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨-202610634,-171984152⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨-171861142,-139824496⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨-139696440,-106503382⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨-106371312,-72291586⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨-72156588,-37472285⟩ :=
  of_check (by decide +kernel)

theorem s31744_128 : Run get 31744 128 ⟨-37335481,-19925747⟩ :=
  of_check (by decide +kernel)

theorem s31872_32 : Run get 31872 32 ⟨-19788469,-15531094⟩ :=
  of_check (by decide +kernel)

theorem s31904_1 : Run get 31904 1 ⟨-15393743,-15393725⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
