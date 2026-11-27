import Point22AtlasRangeGroup410Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s4096_256 : Run get 4096 256 ⟨-794910692,-782809442⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨-802138849,-794948407⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨-804611559,-802157619⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨-804614536,-802547301⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨-802530678,-796202996⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨-796170204,-785868396⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨-785820622,-771860346⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨-771798873,-754516870⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨-754443054,-734191286⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨-734106527,-711246413⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨-711152140,-686049021⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨-685946669,-658964576⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨-658855563,-630352370⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨-630238080,-600561112⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨-600442885,-569925017⟩ :=
  of_check (by decide +kernel)

theorem s7936_128 : Run get 7936 128 ⟨-569804121,-554389787⟩ :=
  of_check (by decide +kernel)

theorem s8064_16 : Run get 8064 16 ⟨-554268011,-552440508⟩ :=
  of_check (by decide +kernel)

theorem s8080_1 : Run get 8080 1 ⟨-552318641,-552318629⟩ :=
  of_check (by decide +kernel)

theorem s7936_256 : Run get 7936 256 ⟨-569804121,-538760415⟩ :=
  of_check (by decide +kernel)

theorem s8064_32 : Run get 8064 32 ⟨-554268011,-550489829⟩ :=
  of_check (by decide +kernel)

theorem s8096_16 : Run get 8096 16 ⟨-550367879,-548537824⟩ :=
  of_check (by decide +kernel)

theorem s8112_1 : Run get 8112 1 ⟨-548415796,-548415784⟩ :=
  of_check (by decide +kernel)

theorem s8080_16 : Run get 8080 16 ⟨-552318641,-550489829⟩ :=
  of_check (by decide +kernel)

theorem s8096_32 : Run get 8096 32 ⟨-550367879,-546584568⟩ :=
  of_check (by decide +kernel)

theorem s8128_64 : Run get 8128 64 ⟨-546462461,-538760415⟩ :=
  of_check (by decide +kernel)

theorem s8112_16 : Run get 8112 16 ⟨-548415796,-546584568⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
