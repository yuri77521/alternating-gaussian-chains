import Point22AtlasRangeGroup110Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s12288_256 : Run get 12288 256 ⟨3433866024,3924316641⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨2997882132,3432056116⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨2613802911,2996283751⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨2277313422,2612398627⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨1984409134,2276086974⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨1731414501,1983345516⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨1514997351,1730500018⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨1332179733,1514219677⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨1180345795,1331527940⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨1057247286,1179810382⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨961007207,1056820199⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨890122077,960681844⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨843463234,889893299⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨820277513,843327369⟩ :=
  of_check (by decide +kernel)

theorem s15872_64 : Run get 15872 64 ⟨818096276,820232355⟩ :=
  of_check (by decide +kernel)

theorem s15936_1 : Run get 15936 1 ⟨818073619,818073622⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨817354286,820232355⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨820232352,843191858⟩ :=
  of_check (by decide +kernel)

theorem s15872_128 : Run get 15872 128 ⟨817354462,820232355⟩ :=
  of_check (by decide +kernel)

theorem s16000_1 : Run get 16000 1 ⟨817354286,817354289⟩ :=
  of_check (by decide +kernel)

theorem s15936_32 : Run get 15936 32 ⟨817545523,818073622⟩ :=
  of_check (by decide +kernel)

theorem s15968_1 : Run get 15968 1 ⟨817534108,817534111⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
