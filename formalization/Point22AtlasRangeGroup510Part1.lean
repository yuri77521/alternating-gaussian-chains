import Point22AtlasRangeGroup510Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s4096_256 : Run get 4096 256 ⟨67376396266,70517327733⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨64183272009,67363988058⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨60969591556,64170746162⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨57754001348,60957022535⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨54554205723,57741460245⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨51386822931,54541759650⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨48267263765,51374534509⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨45209633560,48255190689⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨42226657775,45197828262⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨39329631010,42215167187⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨36528388731,39318496400⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨33831300744,36517645642⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨31245285005,33820979009⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨28775840101,31235408838⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨26427094530,28766428255⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨24201870706,26418160528⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
