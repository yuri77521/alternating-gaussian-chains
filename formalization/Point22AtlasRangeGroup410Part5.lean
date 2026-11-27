import Point22AtlasRangeGroup410Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf410
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 4 1 .value

theorem s20480_256 : Run get 20480 256 ⟨178765579,198386424⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨198466035,219455241⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨219540226,241896985⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨241987307,265692886⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨265788438,290804406⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨290904994,317171548⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨317276895,344711321⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨344821053,373316398⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨373430049,402854041⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨402971038,433165318⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨433284992,464064707⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨464186280,495340090⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨495462682,526753220⟩ :=
  of_check (by decide +kernel)

theorem s23808_128 : Run get 23808 128 ⟨526875848,542430069⟩ :=
  of_check (by decide +kernel)

theorem s23936_32 : Run get 23936 32 ⟨542552319,546340339⟩ :=
  of_check (by decide +kernel)

theorem s23968_16 : Run get 23968 16 ⟨546462449,548293748⟩ :=
  of_check (by decide +kernel)

theorem s23984_1 : Run get 23984 1 ⟨548415784,548415796⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨526875848,558040683⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨558162273,588915397⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨589034782,619068646⟩ :=
  of_check (by decide +kernel)

theorem s23984_16 : Run get 23984 16 ⟨548415784,550245910⟩ :=
  of_check (by decide +kernel)

theorem s24000_64 : Run get 24000 64 ⟨550367867,558040683⟩ :=
  of_check (by decide +kernel)

theorem s24016_16 : Run get 24016 16 ⟨552318629,554146219⟩ :=
  of_check (by decide +kernel)

theorem s24032_32 : Run get 24032 32 ⟨554267999,558040683⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf410
