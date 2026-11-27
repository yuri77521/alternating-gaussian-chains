import Point22AtlasRangeGroup420Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s4096_256 : Run get 4096 256 ⟨1169993,1791802⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨565057,1167614⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨-14848,562764⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨-564634,-17034⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨-1079879,-566691⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨-1556880,-1081796⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨-1992664,-1558640⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨-2384998,-1994258⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨-2732386,-2386421⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨-3034030,-2733629⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨-3289816,-3035093⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨-3500259,-3290701⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨-3666448,-3500970⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨-3789992,-3666987⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨-3872958,-3790373⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨-3917781,-3873182⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
