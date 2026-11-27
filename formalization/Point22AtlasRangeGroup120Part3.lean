import Point22AtlasRangeGroup120Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf120
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 2 .value

theorem s12288_256 : Run get 12288 256 ⟨57491203,64785551⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨50757082,57463778⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨44578554,50731895⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨38917992,44555466⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨33735198,38896850⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨28987958,33715841⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨24632520,28970217⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨20624001,24616223⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨16916706,20608969⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨13464396,16902760⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨10220483,13451356⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨7138170,10208166⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨4170546,7126391⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨1270648,4159123⟩ :=
  of_check (by decide +kernel)

theorem s15872_64 : Run get 15872 64 ⟨550750,1259398⟩ :=
  of_check (by decide +kernel)

theorem s15936_1 : Run get 15936 1 ⟨539508,539514⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨-1608508,1259398⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨-4513913,-1619770⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf120
