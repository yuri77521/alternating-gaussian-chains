import Point22AtlasRangeGroup212Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf212
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .second

theorem s16384_256 : Run get 16384 256 ⟨1055379727,1786357540⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨1789222984,2519405316⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨2522266201,3250754025⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨3253605802,3978927208⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨3981762783,4701723979⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨4704533152,5416083276⟩ :=
  of_check (by decide +kernel)

theorem s17920_32 : Run get 17920 32 ⟨5418852242,5504595107⟩ :=
  of_check (by decide +kernel)

theorem s17952_4 : Run get 17952 4 ⟨5507357878,5515645028⟩ :=
  of_check (by decide +kernel)

theorem s17956_1 : Run get 17956 1 ⟨5518407005,5518407011⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨5418852242,6117965312⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨6120676233,6802253677⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨6804884354,7462681641⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨7465205269,8091786116⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨8094171165,8680892742⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨8683102966,9220135321⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨9222129906,9698512567⟩ :=
  of_check (by decide +kernel)

theorem s19712_128 : Run get 19712 128 ⟨9700246426,9911151321⟩ :=
  of_check (by decide +kernel)

theorem s19840_64 : Run get 19840 64 ⟨9912736695,10010145311⟩ :=
  of_check (by decide +kernel)

theorem s19904_32 : Run get 19904 32 ⟨10011651721,10057722186⟩ :=
  of_check (by decide +kernel)

theorem s19936_8 : Run get 19936 8 ⟨10059187913,10069412039⟩ :=
  of_check (by decide +kernel)

theorem s19944_1 : Run get 19944 1 ⟨10070867468,10070867474⟩ :=
  of_check (by decide +kernel)

theorem s17920_64 : Run get 17920 64 ⟨5418852242,5592904332⟩ :=
  of_check (by decide +kernel)

theorem s17984_4 : Run get 17984 4 ⟨5595660623,5603928278⟩ :=
  of_check (by decide +kernel)

theorem s17988_1 : Run get 17988 1 ⟨5606683740,5606683746⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨9700246426,10103984643⟩ :=
  of_check (by decide +kernel)

theorem s19968_8 : Run get 19968 8 ⟨10105408876,10115341837⟩ :=
  of_check (by decide +kernel)

theorem s19976_1 : Run get 19976 1 ⟨10116755570,10116755576⟩ :=
  of_check (by decide +kernel)

theorem s17984_32 : Run get 17984 32 ⟨5595660623,5681001653⟩ :=
  of_check (by decide +kernel)

theorem s18016_4 : Run get 18016 4 ⟨5683751171,5691998446⟩ :=
  of_check (by decide +kernel)

theorem s18020_1 : Run get 18020 1 ⟨5694747095,5694747101⟩ :=
  of_check (by decide +kernel)

theorem s19968_32 : Run get 19968 32 ⟨10105408876,10148906694⟩ :=
  of_check (by decide +kernel)

theorem s20000_8 : Run get 20000 8 ⟨10150288619,10159924708⟩ :=
  of_check (by decide +kernel)

theorem s20008_1 : Run get 20008 1 ⟨10161295928,10161295934⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨10105408876,10423611410⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨10424673928,10643733555⟩ :=
  of_check (by decide +kernel)

theorem s19968_64 : Run get 19968 64 ⟨10105408876,10192462181⟩ :=
  of_check (by decide +kernel)

theorem s20032_8 : Run get 20032 8 ⟨10193800977,10203134444⟩ :=
  of_check (by decide +kernel)

theorem s20040_1 : Run get 20040 1 ⟨10204462329,10204462335⟩ :=
  of_check (by decide +kernel)

theorem s17956_4 : Run get 17956 4 ⟨5518407005,5526691766⟩ :=
  of_check (by decide +kernel)

theorem s17960_8 : Run get 17960 8 ⟨5529452945,5548775619⟩ :=
  of_check (by decide +kernel)

theorem s17968_16 : Run get 17968 16 ⟨5551535188,5592904332⟩ :=
  of_check (by decide +kernel)

theorem s17984_64 : Run get 17984 64 ⟨5595660623,5768877503⟩ :=
  of_check (by decide +kernel)

theorem s18048_128 : Run get 18048 128 ⟨5771619943,6117965312⟩ :=
  of_check (by decide +kernel)

theorem s17988_4 : Run get 17988 4 ⟨5606683740,5614948897⟩ :=
  of_check (by decide +kernel)

theorem s17992_8 : Run get 17992 8 ⟨5617703523,5636980072⟩ :=
  of_check (by decide +kernel)

theorem s18000_16 : Run get 18000 16 ⟨5639733014,5681001653⟩ :=
  of_check (by decide +kernel)

theorem s18016_32 : Run get 18016 32 ⟨5683751171,5768877503⟩ :=
  of_check (by decide +kernel)

theorem s18020_4 : Run get 18020 4 ⟨5694747095,5702991758⟩ :=
  of_check (by decide +kernel)

theorem s18024_8 : Run get 18024 8 ⟨5705739535,5724967871⟩ :=
  of_check (by decide +kernel)

theorem s18032_16 : Run get 18032 16 ⟨5727713887,5768877503⟩ :=
  of_check (by decide +kernel)

theorem s19944_8 : Run get 19944 8 ⟨10070867468,10081019336⟩ :=
  of_check (by decide +kernel)

theorem s19952_16 : Run get 19952 16 ⟨10082464418,10103984643⟩ :=
  of_check (by decide +kernel)

theorem s19976_8 : Run get 19976 8 ⟨10116755570,10126614850⟩ :=
  of_check (by decide +kernel)

theorem s19984_16 : Run get 19984 16 ⟨10128018031,10148906694⟩ :=
  of_check (by decide +kernel)

theorem s20000_32 : Run get 20000 32 ⟨10150288619,10192462181⟩ :=
  of_check (by decide +kernel)

theorem s20032_64 : Run get 20032 64 ⟨10193800977,10275367959⟩ :=
  of_check (by decide +kernel)

theorem s20096_128 : Run get 20096 128 ⟨10276618016,10423611410⟩ :=
  of_check (by decide +kernel)

theorem s20008_8 : Run get 20008 8 ⟨10161295928,10170856900⟩ :=
  of_check (by decide +kernel)

theorem s20016_16 : Run get 20016 16 ⟨10172217364,10192462181⟩ :=
  of_check (by decide +kernel)

theorem s20040_8 : Run get 20040 8 ⟨10204462329,10213719240⟩ :=
  of_check (by decide +kernel)

theorem s20048_16 : Run get 20048 16 ⟨10215036162,10234624768⟩ :=
  of_check (by decide +kernel)

theorem s20064_32 : Run get 20064 32 ⟨10235919611,10275367959⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf212
