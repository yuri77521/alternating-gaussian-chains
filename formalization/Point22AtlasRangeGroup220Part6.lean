import Point22AtlasRangeGroup220Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s24576_256 : Run get 24576 256 ⟨-1842529,-1762585⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨-1762241,-1660345⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨-1659913,-1535487⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨-1534965,-1387712⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨-1387103,-1217039⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨-1216340,-1023814⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨-1023029,-808744⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨-807875,-572891⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨-571945,-317696⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨-316675,-44961⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨-43876,243151⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨244292,544138⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨545323,855180⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨856398,1173174⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨1174413,1494777⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨1496022,1816446⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
