import Point22AtlasRangeGroup110Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s8192_256 : Run get 8192 256 ⟨21590470673,23650870777⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨19647302925,21582636138⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨17828844051,19639957819⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨16133323865,17821983184⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨14558156056,16126938653⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨13100044684,14552234935⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨11755090188,13094573527⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨10518893293,11750052717⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨9386655435,10514271475⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨8353274529,9382429871⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨7413435126,8349424813⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨6561692217,7409940188⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨5792548172,6558530638⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨5100522469,5789698466⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨4480214084,5097963345⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨3926356577,4477924676⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
