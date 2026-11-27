import Point22AtlasRangeGroup330Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s8192_256 : Run get 8192 256 ⟨21594396714,23654791702⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨19651202203,21586562160⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨17832687768,19643856957⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨16137086509,17825826655⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨14561815458,16130700960⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨13103581984,14555893919⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨11758489775,13098110340⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨10522142704,11753451766⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨9389745195,10517520302⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨8356197986,9385519015⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨7416188249,8352347633⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨6564273377,7412692665⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨5794957920,6561111152⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨5102763311,5792107574⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨4482290237,5100203555⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨3928273763,4480000219⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
