import Point22AtlasRangeGroup210Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s8192_256 : Run get 8192 256 ⟨-267360846,-251717576⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨-251656223,-236049260⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨-235988297,-220539564⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨-220479444,-205297953⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨-205239077,-190420623⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨-190363342,-175990457⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨-175935068,-162077168⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨-162023916,-148737642⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨-148686728,-136016450⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨-135968023,-123946477⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨-123900644,-112549674⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨-112506500,-101837885⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨-101797397,-91813724⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨-91775916,-82471488⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨-82436324,-73798082⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨-73765495,-65773914⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
