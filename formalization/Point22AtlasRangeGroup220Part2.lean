import Point22AtlasRangeGroup220Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s8192_256 : Run get 8192 256 ⟨-1964146,-1960586⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨-1963135,-1949752⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨-1949683,-1921956⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨-1921834,-1881410⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨-1881240,-1829773⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨-1829564,-1768709⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨-1768467,-1699843⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨-1699571,-1624742⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨-1624451,-1544907⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨-1544600,-1461746⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨-1461429,-1376568⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨-1376245,-1290578⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨-1290253,-1204866⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨-1204544,-1120402⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨-1120090,-1038054⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨-1037750,-958564⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
