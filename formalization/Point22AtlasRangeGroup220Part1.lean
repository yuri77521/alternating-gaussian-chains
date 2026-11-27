import Point22AtlasRangeGroup220Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s4096_256 : Run get 4096 256 ⟨546520,856410⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨245444,545335⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨-42778,244304⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨-315643,-43864⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨-570983,-316663⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨-806993,-571933⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨-1022231,-807863⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨-1215628,-1023017⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨-1386480,-1216328⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨-1534432,-1387091⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨-1659470,-1534953⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨-1761885,-1659901⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨-1842259,-1762229⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨-1901425,-1842517⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨-1940444,-1901605⟩ :=
  of_check (by decide +kernel)

theorem s7936_64 : Run get 7936 64 ⟨-1947191,-1940547⟩ :=
  of_check (by decide +kernel)

theorem s8000_16 : Run get 8000 16 ⟨-1948698,-1947276⟩ :=
  of_check (by decide +kernel)

theorem s8016_1 : Run get 8016 1 ⟨-1948788,-1948776⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨-1960556,-1940547⟩ :=
  of_check (by decide +kernel)

theorem s8016_16 : Run get 8016 16 ⟨-1950130,-1948776⟩ :=
  of_check (by decide +kernel)

theorem s8032_32 : Run get 8032 32 ⟨-1952779,-1950205⟩ :=
  of_check (by decide +kernel)

theorem s8064_128 : Run get 8064 128 ⟨-1960556,-1952844⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
