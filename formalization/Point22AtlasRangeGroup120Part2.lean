import Point22AtlasRangeGroup120Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s8192_256 : Run get 8192 256 ⟨249754424,265400254⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨234099502,249693094⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨218617602,234038620⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨203416537,218557616⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨188590844,203357843⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨174221742,188533784⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨160377319,174166607⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨147112894,160324351⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨134471537,147062283⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨122484725,134423429⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨111173100,122439221⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨100547301,111130261⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨90608852,100507150⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨81351080,90571378⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨72760022,81316240⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨64815344,72727751⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
