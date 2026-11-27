import Point22AtlasRangeGroup320Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s20480_256 : Run get 20480 256 ⟨-100477758,-90582010⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨-111098159,-100517886⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨-122404292,-111140977⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨-134385576,-122449776⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨-147021438,-134433662⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨-160280476,-147072025⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨-174119703,-160333419⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨-188483891,-174174813⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨-203305046,-188540926⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨-218502052,-203363719⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨-233980477,-218562015⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨-249632611,-234041337⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨-265337733,-249693920⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨-280962619,-265398997⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨-296362318,-281023293⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨-311381217,-296421813⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
