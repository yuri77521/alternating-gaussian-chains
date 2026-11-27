import Point22AtlasRangeGroup310Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf310
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .value

theorem s4096_256 : Run get 4096 256 ⟨66980207309,70127813640⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨63782860612,66967777814⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨60567359621,63770323036⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨57352246724,60554788062⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨54155102338,57339711828⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨50992403647,54142670698⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨47879406112,50980137303⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨44830048398,47867362127⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨41856880924,44818278536⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨38971017778,41845431420⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨36182111262,38959929188⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨33498348032,36171418412⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨30926465389,33488080041⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨28471786035,30916645776⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨26138269366,28462432876⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨23928577240,26129395540⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf310
