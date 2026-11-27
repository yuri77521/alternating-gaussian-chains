import Point22AtlasRangeGroup210Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s24576_256 : Run get 24576 256 ⟨311447439,325865589⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨325920836,339623157⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨339675251,352483930⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨352532166,364265729⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨364309389,374785072⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨374823442,383859758⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨383892132,391311608⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨391337301,396969336⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨396987696,400671481⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨400681903,402269369⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨401630014,402324972⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨398638957,401622980⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨393202868,398622538⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨385251991,393176745⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨374742265,385215941⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨361657104,374696168⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
