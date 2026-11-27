import Point22AtlasRangeGroup410Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s24576_256 : Run get 24576 256 ⟨619184582,648172692⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨648283866,675883944⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨675988986,701846663⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨701944167,725697198⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨725785730,747068675⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨747146805,765596121⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨765662432,780921907⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨780975026,792701464⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨792740078,800609138⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨800632021,804344107⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨803636208,804614536⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨798251640,803624425⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨787998219,798221182⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨772730329,787948424⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨752353245,772660727⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨726826778,752263569⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
