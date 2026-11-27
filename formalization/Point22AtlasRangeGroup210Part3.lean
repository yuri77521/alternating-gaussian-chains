import Point22AtlasRangeGroup210Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf210
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .value

theorem s12288_256 : Run get 12288 256 ⟨-65743818,-58373788⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨-58346072,-51567723⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨-51542264,-45321745⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨-45298403,-39598588⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨-39577213,-34358346⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨-34338774,-29559027⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨-29541093,-25157049⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨-25140580,-21107649⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨-21092469,-17365221⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨-17351150,-13883581⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨-13870437,-10616175⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨-10603776,-7516224⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨-7504388,-4536832⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨-4525375,-1631038⟩ :=
  of_check (by decide +kernel)

theorem s15872_64 : Run get 15872 64 ⟨-1619776,-910583⟩ :=
  of_check (by decide +kernel)

theorem s15936_32 : Run get 15936 32 ⟨-899341,-550750⟩ :=
  of_check (by decide +kernel)

theorem s15968_1 : Run get 15968 1 ⟨-539514,-539508⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨-1619776,1248142⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨1259392,4147695⟩ :=
  of_check (by decide +kernel)

theorem s15872_128 : Run get 15872 128 ⟨-1619776,-191058⟩ :=
  of_check (by decide +kernel)

theorem s16000_1 : Run get 16000 1 ⟨-179825,-179819⟩ :=
  of_check (by decide +kernel)

theorem s16000_32 : Run get 16000 32 ⟨-179825,168585⟩ :=
  of_check (by decide +kernel)

theorem s16032_1 : Run get 16032 1 ⟨179819,179825⟩ :=
  of_check (by decide +kernel)

theorem s16000_64 : Run get 16000 64 ⟨-179825,528273⟩ :=
  of_check (by decide +kernel)

theorem s16064_1 : Run get 16064 1 ⟨539508,539514⟩ :=
  of_check (by decide +kernel)

theorem s15968_32 : Run get 15968 32 ⟨-539514,-191058⟩ :=
  of_check (by decide +kernel)

theorem s16000_128 : Run get 16000 128 ⟨-179825,1248142⟩ :=
  of_check (by decide +kernel)

theorem s16032_32 : Run get 16032 32 ⟨179819,528273⟩ :=
  of_check (by decide +kernel)

theorem s16064_64 : Run get 16064 64 ⟨539508,1248142⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf210
