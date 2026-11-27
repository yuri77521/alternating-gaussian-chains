import Point22AtlasRangeGroup510Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s8192_256 : Run get 8192 256 ⟨22101761486,24193423108⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨20127217024,22093804213⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨18277639661,20119749716⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨16551484686,18270658061⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨14946364846,16544981037⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨13459156610,14940328310⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨12086106379,13453573682⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨10822934995,12080961300⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨9664939087,10818210152⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨8607088066,9660615404⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨7644115714,8603145372⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨6770605614,7640533090⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨5981069824,6767361715⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨5270020420,5978143168⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨4632033721,5267389654⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨4061807202,4629677864⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
