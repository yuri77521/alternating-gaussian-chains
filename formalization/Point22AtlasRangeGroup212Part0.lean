import Point22AtlasRangeGroup211

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf212
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .second

theorem s64_64 : Run get 64 64 ⟨871120412,2013743514⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨2031869116,4328946928⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨4346985088,8905636488⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨8923310573,13357580509⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨13374644732,17623278949⟩ :=
  of_check (by decide +kernel)

theorem s1024_32 : Run get 1024 32 ⟨17639499448,18140466499⟩ :=
  of_check (by decide +kernel)

theorem s1056_2 : Run get 1056 2 ⟨18156565860,18172661394⟩ :=
  of_check (by decide +kernel)

theorem s1058_1 : Run get 1058 1 ⟨18188753072,18188753078⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨17639499448,21644863912⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨21660023236,25369196766⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨25383097940,28748847573⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨28761317666,31742933745⟩ :=
  of_check (by decide +kernel)

theorem s2048_4 : Run get 2048 4 ⟨31753826843,31786467702⟩ :=
  of_check (by decide +kernel)

theorem s2052_1 : Run get 2052 1 ⟨31797335155,31797335161⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨31753826843,34317799026⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨34326998547,36447518684⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨36454939003,38114221901⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨38119809239,39308227572⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨39311960168,40027995067⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨40029882620,40279896490⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨40077821776,40280428501⟩ :=
  of_check (by decide +kernel)

theorem s3840_128 : Run get 3840 128 ⟨39812807957,40076167466⟩ :=
  of_check (by decide +kernel)

theorem s3968_64 : Run get 3968 64 ⟨39640649617,39810319111⟩ :=
  of_check (by decide +kernel)

theorem s4032_8 : Run get 4032 8 ⟨39617302395,39637753300⟩ :=
  of_check (by decide +kernel)

theorem s4040_1 : Run get 4040 1 ⟨39614355625,39614355631⟩ :=
  of_check (by decide +kernel)

theorem s96_32 : Run get 96 32 ⟨1451654427,2013743514⟩ :=
  of_check (by decide +kernel)

theorem s2048_32 : Run get 2048 32 ⟨31753826843,32088325711⟩ :=
  of_check (by decide +kernel)

theorem s2080_4 : Run get 2080 4 ⟨32099012865,32131035557⟩ :=
  of_check (by decide +kernel)

theorem s2084_1 : Run get 2084 1 ⟨32141696842,32141696848⟩ :=
  of_check (by decide +kernel)

theorem s4032_32 : Run get 4032 32 ⟨39544845089,39637753300⟩ :=
  of_check (by decide +kernel)

theorem s4064_8 : Run get 4064 8 ⟨39519890405,39541747645⟩ :=
  of_check (by decide +kernel)

theorem s4072_1 : Run get 4072 1 ⟨39516742952,39516742958⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨39442632211,40076167466⟩ :=
  of_check (by decide +kernel)

theorem s1058_2 : Run get 1058 2 ⟨18188753072,18204840915⟩ :=
  of_check (by decide +kernel)

theorem s1060_4 : Run get 1060 4 ⟨18220924898,18269153735⟩ :=
  of_check (by decide +kernel)

theorem s1064_8 : Run get 1064 8 ⟨18285222285,18397593742⟩ :=
  of_check (by decide +kernel)

theorem s1072_16 : Run get 1072 16 ⟨18413631270,18653725366⟩ :=
  of_check (by decide +kernel)

theorem s1088_64 : Run get 1088 64 ⟨18669700224,19668029735⟩ :=
  of_check (by decide +kernel)

theorem s1152_128 : Run get 1152 128 ⟨19683745637,21644863912⟩ :=
  of_check (by decide +kernel)

theorem s2052_4 : Run get 2052 4 ⟨31797335155,31829899037⟩ :=
  of_check (by decide +kernel)

theorem s2056_8 : Run get 2056 8 ⟨31840740818,31916453396⟩ :=
  of_check (by decide +kernel)

theorem s2064_16 : Run get 2064 16 ⟨31927243746,32088325711⟩ :=
  of_check (by decide +kernel)

theorem s2080_32 : Run get 2080 32 ⟨32099012865,32427099973⟩ :=
  of_check (by decide +kernel)

theorem s2112_64 : Run get 2112 64 ⟨32437579419,33084575185⟩ :=
  of_check (by decide +kernel)

theorem s2176_128 : Run get 2176 128 ⟨33094634162,34317799026⟩ :=
  of_check (by decide +kernel)

theorem s2816_128 : Run get 2816 128 ⟨38119809239,38770597191⟩ :=
  of_check (by decide +kernel)

theorem s2944_64 : Run get 2944 64 ⟨38775257891,39054263393⟩ :=
  of_check (by decide +kernel)

theorem s3008_32 : Run get 3008 32 ⟨39058459978,39184957503⟩ :=
  of_check (by decide +kernel)

theorem s3040_4 : Run get 3040 4 ⟨39188922047,39200772203⟩ :=
  of_check (by decide +kernel)

theorem s3044_2 : Run get 3044 2 ⟨39204707747,39208636053⟩ :=
  of_check (by decide +kernel)

theorem s3046_1 : Run get 3046 1 ⟨39212557098,39212557104⟩ :=
  of_check (by decide +kernel)

theorem s2084_4 : Run get 2084 4 ⟨32141696842,32173641889⟩ :=
  of_check (by decide +kernel)

theorem s2088_8 : Run get 2088 8 ⟨32184277279,32258543571⟩ :=
  of_check (by decide +kernel)

theorem s2096_16 : Run get 2096 16 ⟨32269127088,32427099973⟩ :=
  of_check (by decide +kernel)

theorem s3046_2 : Run get 3046 2 ⟨39212557098,39216470905⟩ :=
  of_check (by decide +kernel)

theorem s3048_8 : Run get 3048 8 ⟨39220377451,39247520345⟩ :=
  of_check (by decide +kernel)

theorem s3056_16 : Run get 3056 16 ⟨39251368899,39308227572⟩ :=
  of_check (by decide +kernel)

theorem s4040_8 : Run get 4040 8 ⟨39593551977,39614355631⟩ :=
  of_check (by decide +kernel)

theorem s4048_16 : Run get 4048 16 ⟨39544845089,39590554874⟩ :=
  of_check (by decide +kernel)

theorem s4064_32 : Run get 4064 32 ⟨39442632211,39541747645⟩ :=
  of_check (by decide +kernel)

theorem s4072_8 : Run get 4072 8 ⟨39494536092,39516742958⟩ :=
  of_check (by decide +kernel)

theorem s4080_16 : Run get 4080 16 ⟨39442632211,39491338755⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf212
