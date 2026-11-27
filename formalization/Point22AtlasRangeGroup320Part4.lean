import Point22AtlasRangeGroup320Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s16384_256 : Run get 16384 256 ⟨-7116401,-4160168⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨-10198369,-7128169⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨-13441568,-10210675⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨-16892797,-13454598⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨-20598643,-16906731⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨-24605348,-20613662⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨-28958600,-24621630⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨-33703293,-28976326⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨-38883178,-33722634⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨-44540478,-38904305⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨-50715400,-44563548⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨-57445579,-50740566⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨-64765466,-57472986⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨-72705594,-64795239⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨-81291836,-72737846⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨-90544559,-81326655⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
