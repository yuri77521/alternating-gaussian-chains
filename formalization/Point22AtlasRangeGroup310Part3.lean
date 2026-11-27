import Point22AtlasRangeGroup310Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf310
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 1 .value

theorem s12288_256 : Run get 12288 256 ⟨3493131683,3991028481⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨3050269252,3491293769⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨2659876019,3048645138⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨2317600156,2658448136⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨2019397519,2316352093⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨1761550806,2018314113⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨1540684438,1760618195⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨1353775828,1539890122⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨1198163606,1353108703⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨1071553398,1197613993⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨972021688,1071113061⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨898018240,971683844⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨848367502,897777566⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨822269356,848220142⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨817713927,822212921⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨819333011,839409333⟩ :=
  of_check (by decide +kernel)

theorem s15872_128 : Run get 15872 128 ⟨817905212,822212921⟩ :=
  of_check (by decide +kernel)

theorem s16000_32 : Run get 16000 32 ⟨817714102,817893803⟩ :=
  of_check (by decide +kernel)

theorem s16032_1 : Run get 16032 1 ⟨817713927,817713936⟩ :=
  of_check (by decide +kernel)

theorem s16000_64 : Run get 16000 64 ⟨817713927,817893803⟩ :=
  of_check (by decide +kernel)

theorem s16064_1 : Run get 16064 1 ⟨817893794,817893803⟩ :=
  of_check (by decide +kernel)

theorem s16064_64 : Run get 16064 64 ⟨817893794,819299459⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf310
