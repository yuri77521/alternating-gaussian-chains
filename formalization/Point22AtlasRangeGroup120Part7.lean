import Point22AtlasRangeGroup120Part6

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s28672_256 : Run get 28672 256 ⟨-359783261,-343874298⟩ :=
  of_check (by decide +kernel)

theorem s28928_256 : Run get 28928 256 ⟨-343806967,-325394259⟩ :=
  of_check (by decide +kernel)

theorem s29184_256 : Run get 29184 256 ⟨-325317239,-304476719⟩ :=
  of_check (by decide +kernel)

theorem s29440_256 : Run get 29440 256 ⟨-304390366,-281228060⟩ :=
  of_check (by decide +kernel)

theorem s29696_256 : Run get 29696 256 ⟨-281132849,-255784262⟩ :=
  of_check (by decide +kernel)

theorem s29952_256 : Run get 29952 256 ⟨-255680781,-228309762⟩ :=
  of_check (by decide +kernel)

theorem s30208_256 : Run get 30208 256 ⟨-228198706,-198995800⟩ :=
  of_check (by decide +kernel)

theorem s30464_256 : Run get 30464 256 ⟨-198877967,-168058272⟩ :=
  of_check (by decide +kernel)

theorem s30720_256 : Run get 30720 256 ⟨-167934550,-135735122⟩ :=
  of_check (by decide +kernel)

theorem s30976_256 : Run get 30976 256 ⟨-135606479,-102283310⟩ :=
  of_check (by decide +kernel)

theorem s31232_256 : Run get 31232 256 ⟨-102150785,-67975427⟩ :=
  of_check (by decide +kernel)

theorem s31488_256 : Run get 31488 256 ⟨-67840110,-33095990⟩ :=
  of_check (by decide +kernel)

theorem s31744_64 : Run get 31744 64 ⟨-32959009,-24320987⟩ :=
  of_check (by decide +kernel)

theorem s31808_32 : Run get 31808 32 ⟨-24183770,-19928383⟩ :=
  of_check (by decide +kernel)

theorem s31840_1 : Run get 31840 1 ⟨-19791075,-19791069⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
