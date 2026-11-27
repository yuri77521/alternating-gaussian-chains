import Point22AtlasRangeGroup310Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf310
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .value

theorem s20480_256 : Run get 20480 256 ⟨5700320979,6456182481⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨6459302984,7296724348⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨7300175435,8224633333⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨8228436445,9245364522⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨9249540788,10364253956⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨10368823880,11586435722⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨11591418848,12916752610⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨12922167160,14359661056⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨14365523552,15919131293⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨15925456153,17598543844⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨17605342982,19400583744⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨19407866144,21327134025⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨21334905332,23379170249⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨23387432357,25556658007⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨25565408673,27858455458⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨27867687929,30282223062⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf310
