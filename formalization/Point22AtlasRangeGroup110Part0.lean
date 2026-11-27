import Point22AtlasFastBlock
import Point22AtlasNodeData

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf110
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .value

theorem s32_32 : Run get 32 32 ⟨99991473270,99997800082⟩ :=
  of_check (by decide +kernel)

theorem s64_64 : Run get 64 64 ⟨99965353910,99991200445⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨99860395447,99964806253⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨99440568598,99859299137⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨98744051638,99438383069⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨97776686150,98740795262⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨96546539447,97772386174⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨95063792555,96541231611⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨93340599923,95057520597⟩ :=
  of_check (by decide +kernel)

theorem s1792_128 : Run get 1792 128 ⟨92393133989,93333414982⟩ :=
  of_check (by decide +kernel)

theorem s1920_64 : Run get 1920 64 ⟨91898749195,92385513858⟩ :=
  of_check (by decide +kernel)

theorem s1984_32 : Run get 1984 32 ⟨91646500840,91890917138⟩ :=
  of_check (by decide +kernel)

theorem s2016_4 : Run get 2016 4 ⟨91614735084,91638564278⟩ :=
  of_check (by decide +kernel)

theorem s2020_1 : Run get 2020 1 ⟨91606785525,91606785528⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨91390923581,93333414982⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨89230344893,91382883500⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨86875857462,89221513447⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨84345645028,86866303514⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨81658848408,84335441638⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨78835325657,81648071911⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨75895409597,78824054710⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨72859666856,75883724241⟩ :=
  of_check (by decide +kernel)

theorem s3840_128 : Run get 3840 128 ⟨71312293343,72847647576⟩ :=
  of_check (by decide +kernel)

theorem s3968_32 : Run get 3968 32 ⟨70922810363,71300137175⟩ :=
  of_check (by decide +kernel)

theorem s4000_8 : Run get 4000 8 ⟨70825285527,70910623085⟩ :=
  of_check (by decide +kernel)

theorem s4008_1 : Run get 4008 1 ⟨70813090663,70813090666⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨69748662317,72847647576⟩ :=
  of_check (by decide +kernel)

theorem s2048_4 : Run get 2048 4 ⟨91358743937,91382883500⟩ :=
  of_check (by decide +kernel)

theorem s2052_1 : Run get 2052 1 ⟨91350690983,91350690986⟩ :=
  of_check (by decide +kernel)

theorem s96_32 : Run get 96 32 ⟨99965353910,99980202018⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf110
