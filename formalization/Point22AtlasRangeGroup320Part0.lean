import Point22AtlasRangeGroup312

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s96_32 : Run get 96 32 ⟨10996966,15256372⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨15393725,32817694⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨32954649,67695876⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨67831172,102004890⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨102137399,135460197⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨135588829,167789161⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨167912878,198734740⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨198852572,228058876⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨228169935,255545527⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨255649015,281003288⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨281098511,304267529⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨304353899,325202069⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨325279106,343700290⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨343767643,359685792⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨359743219,373112465⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨373159846,383964105⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨384001435,392253509⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
