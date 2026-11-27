import Point22AtlasRangeGroup320Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s24576_256 : Run get 24576 256 ⟨-325854380,-311438906⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨-339609157,-325909603⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨-352467081,-339661227⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨-364246007,-352515291⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨-374762500,-364289646⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨-383834397,-374800848⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨-391283568,-383866750⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨-396938768,-391309241⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨-400638587,-396957110⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨-402234394,-400648987⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨-402289570,-401593237⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨-401586207,-398600717⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨-398584306,-393163534⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨-393137422,-385211968⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨-385175929,-374701980⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨-374655898,-361617011⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
