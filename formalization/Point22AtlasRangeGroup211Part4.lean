import Point22AtlasRangeGroup211Part3

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf211
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .first

theorem s16384_256 : Run get 16384 256 ⟨365708378,377031257⟩ :=
  of_check (by decide +kernel)

theorem s16640_256 : Run get 16640 256 ⟨377087119,394255080⟩ :=
  of_check (by decide +kernel)

theorem s16896_256 : Run get 16896 256 ⟨394333850,417337262⟩ :=
  of_check (by decide +kernel)

theorem s17152_256 : Run get 17152 256 ⟨417438886,446258741⟩ :=
  of_check (by decide +kernel)

theorem s17408_256 : Run get 17408 256 ⟨446383121,480985837⟩ :=
  of_check (by decide +kernel)

theorem s17664_256 : Run get 17664 256 ⟨481132804,521463911⟩ :=
  of_check (by decide +kernel)

theorem s17920_32 : Run get 17920 32 ⟨521633201,526924267⟩ :=
  of_check (by decide +kernel)

theorem s17952_4 : Run get 17952 4 ⟨527096323,527613032⟩ :=
  of_check (by decide +kernel)

theorem s17956_1 : Run get 17956 1 ⟨527785433,527785439⟩ :=
  of_check (by decide +kernel)

theorem s17920_256 : Run get 17920 256 ⟨521633201,567609993⟩ :=
  of_check (by decide +kernel)

theorem s18176_256 : Run get 18176 256 ⟨567801215,619304542⟩ :=
  of_check (by decide +kernel)

theorem s18432_256 : Run get 18432 256 ⟨619517148,676382531⟩ :=
  of_check (by decide +kernel)

theorem s18688_256 : Run get 18688 256 ⟨676615772,738624028⟩ :=
  of_check (by decide +kernel)

theorem s18944_256 : Run get 18944 256 ⟨738876927,805744553⟩ :=
  of_check (by decide +kernel)

theorem s19200_256 : Run get 19200 256 ⟨806015860,877385442⟩ :=
  of_check (by decide +kernel)

theorem s19456_256 : Run get 19456 256 ⟨877673596,953104504⟩ :=
  of_check (by decide +kernel)

theorem s19712_128 : Run get 19712 128 ⟨953407603,992330164⟩ :=
  of_check (by decide +kernel)

theorem s19840_64 : Run get 19840 64 ⟨992639907,1012252303⟩ :=
  of_check (by decide +kernel)

theorem s19904_32 : Run get 19904 32 ⟨1012565138,1022286345⟩ :=
  of_check (by decide +kernel)

theorem s19936_8 : Run get 19936 8 ⟨1022600666,1024802239⟩ :=
  of_check (by decide +kernel)

theorem s19944_1 : Run get 19944 1 ⟨1025116924,1025116930⟩ :=
  of_check (by decide +kernel)

theorem s17920_64 : Run get 17920 64 ⟨521633201,532473034⟩ :=
  of_check (by decide +kernel)

theorem s17984_4 : Run get 17984 4 ⟨532647849,533172836⟩ :=
  of_check (by decide +kernel)

theorem s17988_1 : Run get 17988 1 ⟨533347996,533348002⟩ :=
  of_check (by decide +kernel)

theorem s19712_256 : Run get 19712 256 ⟨953407603,1032367309⟩ :=
  of_check (by decide +kernel)

theorem s19968_8 : Run get 19968 8 ⟨1032683075,1034894727⟩ :=
  of_check (by decide +kernel)

theorem s19976_1 : Run get 19976 1 ⟨1035210848,1035210854⟩ :=
  of_check (by decide +kernel)

theorem s17984_32 : Run get 17984 32 ⟨532647849,538110005⟩ :=
  of_check (by decide +kernel)

theorem s18016_4 : Run get 18016 4 ⟨538287574,538820818⟩ :=
  of_check (by decide +kernel)

theorem s18020_1 : Run get 18020 1 ⟨538998729,538998735⟩ :=
  of_check (by decide +kernel)

theorem s19968_32 : Run get 19968 32 ⟨1032683075,1042493868⟩ :=
  of_check (by decide +kernel)

theorem s20000_8 : Run get 20000 8 ⟨1042811037,1045032474⟩ :=
  of_check (by decide +kernel)

theorem s20008_1 : Run get 20008 1 ⟨1045349986,1045349992⟩ :=
  of_check (by decide +kernel)

theorem s19968_256 : Run get 19968 256 ⟨1032683075,1114539401⟩ :=
  of_check (by decide +kernel)

theorem s20224_256 : Run get 20224 256 ⟨1114865150,1198879791⟩ :=
  of_check (by decide +kernel)

theorem s19968_64 : Run get 19968 64 ⟨1032683075,1052664667⟩ :=
  of_check (by decide +kernel)

theorem s20032_8 : Run get 20032 8 ⟨1052983196,1055214118⟩ :=
  of_check (by decide +kernel)

theorem s20040_1 : Run get 20040 1 ⟨1055532982,1055532988⟩ :=
  of_check (by decide +kernel)

theorem s17956_4 : Run get 17956 4 ⟨527785433,528303178⟩ :=
  of_check (by decide +kernel)

theorem s17960_8 : Run get 17960 8 ⟨528475925,529687611⟩ :=
  of_check (by decide +kernel)

theorem s17968_16 : Run get 17968 16 ⟨529861048,532473034⟩ :=
  of_check (by decide +kernel)

theorem s17984_64 : Run get 17984 64 ⟨532647849,543834964⟩ :=
  of_check (by decide +kernel)

theorem s18048_128 : Run get 18048 128 ⟨544015277,567609993⟩ :=
  of_check (by decide +kernel)

theorem s17988_4 : Run get 17988 4 ⟨533347996,533874016⟩ :=
  of_check (by decide +kernel)

theorem s17992_8 : Run get 17992 8 ⟨534049520,535280508⟩ :=
  of_check (by decide +kernel)

theorem s18000_16 : Run get 18000 16 ⟨535456700,538110005⟩ :=
  of_check (by decide +kernel)

theorem s18016_32 : Run get 18016 32 ⟨538287574,543834964⟩ :=
  of_check (by decide +kernel)

theorem s18020_4 : Run get 18020 4 ⟨538998729,539533005⟩ :=
  of_check (by decide +kernel)

theorem s18024_8 : Run get 18024 8 ⟨539711260,540961499⟩ :=
  of_check (by decide +kernel)

theorem s18032_16 : Run get 18032 16 ⟨541140442,543834964⟩ :=
  of_check (by decide +kernel)

theorem s19944_8 : Run get 19944 8 ⟨1025116924,1027321045⟩ :=
  of_check (by decide +kernel)

theorem s19952_16 : Run get 19952 16 ⟨1027636093,1032367309⟩ :=
  of_check (by decide +kernel)

theorem s19976_8 : Run get 19976 8 ⟨1035210848,1037424973⟩ :=
  of_check (by decide +kernel)

theorem s19984_16 : Run get 19984 16 ⟨1037741446,1042493868⟩ :=
  of_check (by decide +kernel)

theorem s20000_32 : Run get 20000 32 ⟨1042811037,1052664667⟩ :=
  of_check (by decide +kernel)

theorem s20032_64 : Run get 20032 64 ⟨1052983196,1073133444⟩ :=
  of_check (by decide +kernel)

theorem s20096_128 : Run get 20096 128 ⟨1073454563,1114539401⟩ :=
  of_check (by decide +kernel)

theorem s20008_8 : Run get 20008 8 ⟨1045349986,1047573823⟩ :=
  of_check (by decide +kernel)

theorem s20016_16 : Run get 20016 16 ⟨1047891678,1052664667⟩ :=
  of_check (by decide +kernel)

theorem s20040_8 : Run get 20040 8 ⟨1055532982,1057766227⟩ :=
  of_check (by decide +kernel)

theorem s20048_16 : Run get 20048 16 ⟨1058085420,1062878328⟩ :=
  of_check (by decide +kernel)

theorem s20064_32 : Run get 20064 32 ⟨1063198174,1073133444⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf211
