import Point22AtlasRangeGroup210Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s16384_256 : Run get 16384 256 ⟨4159117,7114608⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨7126385,10195844⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨10208160,13438313⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨13451350,16888813⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨16902754,20593936⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨20608963,24599924⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨24616217,28952477⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨28970211,33696484⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨33715835,38875710⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨38896844,44532380⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨44555460,50706711⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨50731889,57436355⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨57463772,64755762⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨64785545,72695486⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨72727745,81281406⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨81316234,90533907⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
