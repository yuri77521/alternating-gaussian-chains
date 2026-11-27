import Point22AtlasRangeGroup220Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s12288_256 : Run get 12288 256 ⟨-958273,-882579⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨-882300,-810635⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨-810375,-743185⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨-742943,-680590⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨-680369,-623142⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨-622939,-571063⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨-570882,-524523⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨-524363,-483642⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨-483506,-448509⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨-448396,-419179⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨-419087,-395686⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨-395616,-378048⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨-378003,-366280⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨-366258,-360384⟩ :=
  of_check (by decide +kernel)

theorem s15872_64 : Run get 15872 64 ⟨-360384,-359827⟩ :=
  of_check (by decide +kernel)

theorem s15936_32 : Run get 15936 32 ⟨-359833,-359686⟩ :=
  of_check (by decide +kernel)

theorem s15968_1 : Run get 15968 1 ⟨-359695,-359683⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨-360384,-359637⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨-366224,-360372⟩ :=
  of_check (by decide +kernel)

theorem s15872_128 : Run get 15872 128 ⟨-360384,-359637⟩ :=
  of_check (by decide +kernel)

theorem s16000_1 : Run get 16000 1 ⟨-359650,-359638⟩ :=
  of_check (by decide +kernel)

theorem s15968_32 : Run get 15968 32 ⟨-359695,-359637⟩ :=
  of_check (by decide +kernel)

theorem s16000_128 : Run get 16000 128 ⟨-360372,-359637⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
