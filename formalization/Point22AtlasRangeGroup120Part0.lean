import Point22AtlasRangeGroup112

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s32_32 : Run get 32 32 ⟨6599634,10860987⟩ :=
  of_check (by decide +kernel)

theorem s64_64 : Run get 64 64 ⟨10998424,19653758⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨19791069,37203550⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨37340390,72031022⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨72166061,106253107⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨106385219,139586485⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨139714585,171760212⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨171883271,202519388⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨202636446,231628504⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨231738683,258874425⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨258976939,284068950⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨284163118,307050902⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨307136148,327687723⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨327763586,345876545⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨345942685,361544757⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨361600947,374650027⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨374696162,385179847⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨385215935,393150579⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
