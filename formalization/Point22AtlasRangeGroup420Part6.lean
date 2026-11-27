import Point22AtlasRangeGroup420Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s24576_256 : Run get 24576 256 ⟨-3701781,-3547259⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨-3546591,-3348352⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨-3347510,-3104330⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨-3103308,-2814520⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨-2813323,-2478879⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨-2477503,-2098016⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨-2096468,-1673251⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨-1671534,-1206622⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨-1204746,-700912⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨-698887,-159638⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨-157482,412963⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨415232,1011972⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨1014332,1631823⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨1634251,2266376⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨2268851,2909006⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨2911497,3552669⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
