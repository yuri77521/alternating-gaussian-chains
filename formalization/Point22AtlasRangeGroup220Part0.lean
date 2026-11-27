import Point22AtlasRangeGroup212

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s64_64 : Run get 64 64 ⟨4395373,4398796⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨4381526,4395313⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨4326239,4381393⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨4234861,4325963⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨4108665,4234446⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨3949405,4108118⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨3759279,3948733⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨3540882,3758491⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨3297157,3539989⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨3031346,3296170⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨2746924,3030281⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨2447543,2745794⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨2136948,2446359⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨1818939,2135730⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨1497281,1817698⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨1175665,1496034⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨857630,1174425⟩ :=
  of_check (by decide +kernel)

theorem s96_32 : Run get 96 32 ⟨4395373,4397344⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
