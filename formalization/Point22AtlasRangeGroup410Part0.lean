import Point22AtlasRangeGroup330

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s128_128 : Run get 128 128 ⟨-56868561,-21995396⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨-126730912,-57142767⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨-195527224,-127002088⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨-262685939,-195793102⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨-327658333,-262944327⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨-389925976,-327907141⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨-449007616,-390163250⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨-504465325,-449231556⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨-555909839,-504674314⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨-603004981,-556102456⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨-645471095,-603180021⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨-683087474,-645627583⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨-715693718,-683224663⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨-743190071,-715811101⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨-765536729,-743287377⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨-782752188,-765613916⟩ :=
  of_check (by decide +kernel)

theorem s160_32 : Run get 160 32 ⟨-39304922,-30789493⟩ :=
  of_check (by decide +kernel)

theorem s192_64 : Run get 192 64 ⟨-56868561,-39579526⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
