import Point22AtlasRangeGroup410

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf420
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 2 .value

theorem s128_128 : Run get 128 128 ⟨8771133,8794109⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨8669723,8770903⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨8495888,8669206⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨8252054,8495094⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨7941611,8250993⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨7568849,7940299⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨7138858,7567301⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨6657446,7137097⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨6131029,6655494⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨5566502,6128916⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨4971130,5564256⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨4352389,4968774⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨3717868,4349959⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨3075116,3715391⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨2431534,3072621⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨1794246,2429053⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf420
