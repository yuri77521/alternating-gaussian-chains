import Point22AtlasRangeGroup120Part5

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s24576_256 : Run get 24576 256 ⟨-327628180,-313289962⟩ :=
  of_check (by decide +kernel)

theorem s24832_256 : Run get 24832 256 ⟨-341283508,-327683071⟩ :=
  of_check (by decide +kernel)

theorem s25088_256 : Run get 25088 256 ⟨-354019423,-341335158⟩ :=
  of_check (by decide +kernel)

theorem s25344_256 : Run get 25344 256 ⟨-365653447,-354067125⟩ :=
  of_check (by decide +kernel)

theorem s25600_256 : Run get 25600 256 ⟨-376002117,-365696486⟩ :=
  of_check (by decide +kernel)

theorem s25856_256 : Run get 25856 256 ⟨-384883578,-376039776⟩ :=
  of_check (by decide +kernel)

theorem s26112_256 : Run get 26112 256 ⟨-392120358,-384915155⟩ :=
  of_check (by decide +kernel)

theorem s26368_256 : Run get 26368 256 ⟨-397542233,-392145170⟩ :=
  of_check (by decide +kernel)

theorem s26624_256 : Run get 26624 256 ⟨-400989183,-397559635⟩ :=
  of_check (by decide +kernel)

theorem s26880_256 : Run get 26880 256 ⟨-402314336,-400998572⟩ :=
  of_check (by decide +kernel)

theorem s27136_256 : Run get 27136 256 ⟨-402324972,-401386869⟩ :=
  of_check (by decide +kernel)

theorem s27392_256 : Run get 27392 256 ⟨-401378682,-398094825⟩ :=
  of_check (by decide +kernel)

theorem s27648_256 : Run get 27648 256 ⟨-398077209,-392347694⟩ :=
  of_check (by decide +kernel)

theorem s27904_256 : Run get 27904 256 ⟨-392320341,-384078823⟩ :=
  of_check (by decide +kernel)

theorem s28160_256 : Run get 28160 256 ⟨-384041522,-373247494⟩ :=
  of_check (by decide +kernel)

theorem s28416_256 : Run get 28416 256 ⟨-373200140,-359840664⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
