import Point22AtlasRangeGroup410Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s12288_256 : Run get 12288 256 ⟨-133433489,-118540669⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨-118484654,-104783066⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨-104731597,-92154464⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨-92107265,-80581094⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨-80537866,-69983745⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨-69944166,-60278907⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨-60242646,-51379773⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨-51346486,-43197077⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨-43166411,-35639788⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨-35611386,-28615664⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨-28589162,-22031672⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨-22006705,-15794301⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨-15770505,-9809777⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨-9786785,-3984193⟩ :=
  of_check (by decide +kernel)

theorem s15872_128 : Run get 15872 128 ⟨-3961638,-1101641⟩ :=
  of_check (by decide +kernel)

theorem s16000_32 : Run get 16000 32 ⟨-1079166,-382165⟩ :=
  of_check (by decide +kernel)

theorem s16032_1 : Run get 16032 1 ⟨-359695,-359683⟩ :=
  of_check (by decide +kernel)

theorem s16000_64 : Run get 16000 64 ⟨-1079166,337215⟩ :=
  of_check (by decide +kernel)

theorem s16064_1 : Run get 16064 1 ⟨359683,359695⟩ :=
  of_check (by decide +kernel)

theorem s16032_32 : Run get 16032 32 ⟨-359695,337215⟩ :=
  of_check (by decide +kernel)

theorem s16064_64 : Run get 16064 64 ⟨359683,1776415⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨1798900,7566022⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
