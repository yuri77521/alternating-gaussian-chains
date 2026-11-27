import Point22AtlasRangeGroup330Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s20480_256 : Run get 20480 256 ⟨5792107547,6557950156⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨6561111125,7409198400⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨7412692638,8348498687⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨8352347606,9381294319⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨9385518988,10512899460⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨10517520275,11748415384⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨11753451739,13092640396⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨13098110313,14549974137⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨14555893892,16124317221⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨16130700933,17818967392⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨17825826628,19636513588⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨19643856930,21578729494⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨21586562133,23646468347⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨23654791675,25839560997⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨25848372220,28156719261⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨28166011036,30595446744⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
