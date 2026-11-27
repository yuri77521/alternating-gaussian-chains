import Point22AtlasRangeGroup510Part2

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf510
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 5 1 .value

theorem s12288_256 : Run get 12288 256 ⟨3554209196,4059705844⟩ :=
  of_check (by decide +kernel)

theorem s12544_256 : Run get 12544 256 ⟨3104321710,3552342688⟩ :=
  of_check (by decide +kernel)

theorem s12800_256 : Run get 12800 256 ⟨2707476672,3102671307⟩ :=
  of_check (by decide +kernel)

theorem s13056_256 : Run get 13056 256 ⟨2359286142,2706024670⟩ :=
  of_check (by decide +kernel)

theorem s13312_256 : Run get 13312 256 ⟨2055666991,2358015984⟩ :=
  of_check (by decide +kernel)

theorem s13568_256 : Run get 13568 256 ⟨1792860643,2054563356⟩ :=
  of_check (by decide +kernel)

theorem s13824_256 : Run get 13824 256 ⟨1567448485,1791909505⟩ :=
  of_check (by decide +kernel)

theorem s14080_256 : Run get 14080 256 ⟨1376363564,1566637171⟩ :=
  of_check (by decide +kernel)

theorem s14336_256 : Run get 14336 256 ⟨1216899186,1375680797⟩ :=
  of_check (by decide +kernel)

theorem s14592_256 : Run get 14592 256 ⟨1086714982,1216335107⟩ :=
  of_check (by decide +kernel)

theorem s14848_256 : Run get 14848 256 ⟨983841000,1086261174⟩ :=
  of_check (by decide +kernel)

theorem s15104_256 : Run get 15104 256 ⟨906680297,983490500⟩ :=
  of_check (by decide +kernel)

theorem s15360_256 : Run get 15360 256 ⟨854010459,906427597⟩ :=
  of_check (by decide +kernel)

theorem s15616_256 : Run get 15616 256 ⟨824984424,853851521⟩ :=
  of_check (by decide +kernel)

theorem s15872_256 : Run get 15872 256 ⟨818433302,824916675⟩ :=
  of_check (by decide +kernel)

theorem s16128_256 : Run get 16128 256 ⟨819153186,836354346⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf510
