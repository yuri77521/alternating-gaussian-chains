import Point22AtlasRangeGroup320Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s4096_256 : Run get 4096 256 ⟨392280891,398021153⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨398038800,401333471⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨401341689,402289570⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨400974738,402279952⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨397546112,400965403⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨392141562,397528761⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨384920976,392116800⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨376054460,384889448⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨365719395,376016845⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨354097572,365676400⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨341372410,354049910⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨327726367,341320798⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨313338527,327671510⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨298382426,313281119⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨283024121,298323125⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨267420554,282963565⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
