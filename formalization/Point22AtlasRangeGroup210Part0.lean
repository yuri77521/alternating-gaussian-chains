import Point22AtlasRangeGroup120

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s64_64 : Run get 64 64 ⟨-15258379,-6599634⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨-32822018,-15395762⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨-67704777,-32959003⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨-102018240,-67840104⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨-135477814,-102150779⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨-167810801,-135606473⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨-198760103,-167934544⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨-228087616,-198877961⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨-255577262,-228198700⟩ :=
  of_check (by decide +kernel)

theorem s2048_4 : Run get 2048 4 ⟨-255991150,-255680775⟩ :=
  of_check (by decide +kernel)

theorem s2052_1 : Run get 2052 1 ⟨-256094545,-256094539⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨-281037598,-255680775⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨-304303972,-281132843⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨-325240174,-304390360⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨-343739591,-325317233⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨-359725812,-343806961⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨-373152740,-359783255⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨-384004176,-373200134⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨-392292943,-384041516⟩ :=
  of_check (by decide +kernel)

theorem s96_32 : Run get 96 32 ⟨-15258379,-10998424⟩ :=
  of_check (by decide +kernel)

theorem s160_32 : Run get 160 32 ⟨-24046543,-19791069⟩ :=
  of_check (by decide +kernel)

theorem s192_64 : Run get 192 64 ⟨-32822018,-24183764⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
