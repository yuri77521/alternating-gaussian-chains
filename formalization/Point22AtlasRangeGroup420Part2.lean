import Point22AtlasRangeGroup420Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s8192_256 : Run get 8192 256 ⟨-3928034,-3917860⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨-3927197,-3904266⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨-3904141,-3852122⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨-3851889,-3774061⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨-3773732,-3673404⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨-3672995,-3553479⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨-3553002,-3417547⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨-3417010,-3268760⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨-3268181,-3110138⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨-3109527,-2944520⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨-2943888,-2774551⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨-2773907,-2602669⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨-2602019,-2431078⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨-2430434,-2261755⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨-2261126,-2096453⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨-2095843,-1936695⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
