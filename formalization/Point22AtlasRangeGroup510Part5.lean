import Point22AtlasRangeGroup510Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s20480_256 : Run get 20480 256 ⟨5613299437,6359520749⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨6362602106,7189700230⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨7193109483,8106559392⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨8110317992,9115560363⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨9119689488,10222055898⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨10226576133,11431207316⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨11436138336,12747895957⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨12753256155,14176628817⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨14182434939,15721439275⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨15727706010,17385784017⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨17392523603,19172437508⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨19179659305,21083385527⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨21091095607,23119719533⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨23127920267,25281533741⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨25290223414,27567826987⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨27576999416,29976411504⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
