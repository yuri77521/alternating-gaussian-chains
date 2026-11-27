import Point22AtlasRangeGroup320Part1

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf320
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 2 .value

theorem s8192_256 : Run get 8192 256 ⟨251718151,267359336⟩ :=
  of_check (by decide +kernel)

theorem s8448_256 : Run get 8448 256 ⟨236051748,251656819⟩ :=
  of_check (by decide +kernel)

theorem s8704_256 : Run get 8704 256 ⟨220543766,235990804⟩ :=
  of_check (by decide +kernel)

theorem s8960_256 : Run get 8960 256 ⟨205303655,220483664⟩ :=
  of_check (by decide +kernel)

theorem s9216_256 : Run get 9216 256 ⟨190427623,205244798⟩ :=
  of_check (by decide +kernel)

theorem s9472_256 : Run get 9472 256 ⟨175998546,190370358⟩ :=
  of_check (by decide +kernel)

theorem s9728_256 : Run get 9728 256 ⟨162086142,175943171⟩ :=
  of_check (by decide +kernel)

theorem s9984_256 : Run get 9984 256 ⟨148747313,162032909⟩ :=
  of_check (by decide +kernel)

theorem s10240_256 : Run get 10240 256 ⟨136026632,148696413⟩ :=
  of_check (by decide +kernel)

theorem s10496_256 : Run get 10496 256 ⟨123957000,135978218⟩ :=
  of_check (by decide +kernel)

theorem s10752_256 : Run get 10752 256 ⟨112560383,123911179⟩ :=
  of_check (by decide +kernel)

theorem s11008_256 : Run get 11008 256 ⟨101848633,112517221⟩ :=
  of_check (by decide +kernel)

theorem s11264_256 : Run get 11264 256 ⟨91824381,101808159⟩ :=
  of_check (by decide +kernel)

theorem s11520_256 : Run get 11520 256 ⟨82481943,91786586⟩ :=
  of_check (by decide +kernel)

theorem s11776_256 : Run get 11776 256 ⟨73808228,82446787⟩ :=
  of_check (by decide +kernel)

theorem s12032_256 : Run get 12032 256 ⟨65783667,73775651⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf320
