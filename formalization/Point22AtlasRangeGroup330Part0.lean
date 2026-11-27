import Point22AtlasRangeGroup320

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf330
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 3 3 .value

theorem s96_32 : Run get 96 32 ⟨99956563721,99971407933⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨99851632946,99956016232⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨99431916658,99850536948⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨98735582439,99429731726⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨97768469314,98732326939⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨96538641093,97764170481⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨95056274414,96533334650⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨93333518536,95050004080⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨91384329592,93326335428⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨89224282470,91376291528⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨86870363820,89215453202⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨84340750098,86860812183⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨81654574604,84330549117⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨78831687814,81643800591⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨75892415007,78820419394⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨72857315446,75880732191⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨69746946928,72845298693⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf330
