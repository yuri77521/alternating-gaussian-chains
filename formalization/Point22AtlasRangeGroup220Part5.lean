import Point22AtlasRangeGroup220Part4

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf220
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 2 .value

theorem s20480_256 : Run get 20480 256 ⟨-1289918,-1204532⟩ :=
  of_check (by decide +kernel)

theorem s20736_256 : Run get 20736 256 ⟨-1375909,-1290241⟩ :=
  of_check (by decide +kernel)

theorem s20992_256 : Run get 20992 256 ⟨-1461097,-1376233⟩ :=
  of_check (by decide +kernel)

theorem s21248_256 : Run get 21248 256 ⟨-1544280,-1461417⟩ :=
  of_check (by decide +kernel)

theorem s21504_256 : Run get 21504 256 ⟨-1624147,-1544588⟩ :=
  of_check (by decide +kernel)

theorem s21760_256 : Run get 21760 256 ⟨-1699290,-1624439⟩ :=
  of_check (by decide +kernel)

theorem s22016_256 : Run get 22016 256 ⟨-1768213,-1699559⟩ :=
  of_check (by decide +kernel)

theorem s22272_256 : Run get 22272 256 ⟨-1829344,-1768455⟩ :=
  of_check (by decide +kernel)

theorem s22528_256 : Run get 22528 256 ⟨-1881058,-1829552⟩ :=
  of_check (by decide +kernel)

theorem s22784_256 : Run get 22784 256 ⟨-1921699,-1881228⟩ :=
  of_check (by decide +kernel)

theorem s23040_256 : Run get 23040 256 ⟨-1949601,-1921822⟩ :=
  of_check (by decide +kernel)

theorem s23296_256 : Run get 23296 256 ⟨-1963113,-1949671⟩ :=
  of_check (by decide +kernel)

theorem s23552_256 : Run get 23552 256 ⟨-1964146,-1960629⟩ :=
  of_check (by decide +kernel)

theorem s23808_256 : Run get 23808 256 ⟨-1960598,-1940660⟩ :=
  of_check (by decide +kernel)

theorem s24064_256 : Run get 24064 256 ⟨-1940559,-1901796⟩ :=
  of_check (by decide +kernel)

theorem s24320_256 : Run get 24320 256 ⟨-1901617,-1842789⟩ :=
  of_check (by decide +kernel)

theorem s23808_64 : Run get 23808 64 ⟨-1960598,-1957334⟩ :=
  of_check (by decide +kernel)

theorem s23872_32 : Run get 23872 32 ⟨-1957286,-1955269⟩ :=
  of_check (by decide +kernel)

theorem s23904_16 : Run get 23904 16 ⟨-1955213,-1954131⟩ :=
  of_check (by decide +kernel)

theorem s23920_1 : Run get 23920 1 ⟨-1954069,-1954057⟩ :=
  of_check (by decide +kernel)

theorem s23920_16 : Run get 23920 16 ⟨-1954069,-1952924⟩ :=
  of_check (by decide +kernel)

theorem s23936_128 : Run get 23936 128 ⟨-1952856,-1940660⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf220
