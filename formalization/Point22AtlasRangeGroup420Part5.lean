import Point22AtlasRangeGroup420Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s20480_256 : Run get 20480 256 ⟨-2558342,-2387797⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨-2730351,-2558989⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨-2901036,-2731000⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨-3068022,-2901678⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨-3228714,-3068641⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨-3380319,-3229302⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨-3519862,-3380863⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨-3644223,-3520355⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨-3750160,-3644649⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨-3834369,-3750512⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨-3893512,-3834627⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨-3924285,-3893665⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨-3928034,-3923459⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨-3923415,-3888033⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨-3887847,-3815150⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨-3814813,-3702280⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
