import Point22AtlasRangeGroup310Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf310
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .value

theorem s16384_256 : Run get 16384 256 ⟨839533438,882926438⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨883143112,950554037⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨950866764,1043370939⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨1043784667,1162830883⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨1163352026,1310761336⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨1311397763,1489361363⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨1490122389,1701198185⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨1702094553,1949201941⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨1950245800,2236658150⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨2237863017,2567197282⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨2568578001,2944780868⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨2946353539,3373683504⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨3375465409,3858470147⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨3860479654,4403968123⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨4406224559,5015233246⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨5017756759,5697509592⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf310
