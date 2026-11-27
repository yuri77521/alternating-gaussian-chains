import Point22AtlasRangeGroup120Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s4096_256 : Run get 4096 256 ⟨393176739,398606076⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨398622532,401615903⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨401622974,402324972⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨400692298,402271305⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨397006034,400681909⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨391362973,396987702⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨383924487,391337307⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨374861796,383892138⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨364353037,374823448⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨352580391,364309395⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨339727337,352532172⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨325976077,339675257⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨311505148,325920842⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨296487281,311447445⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨281087506,296427770⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨265461536,281026815⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
