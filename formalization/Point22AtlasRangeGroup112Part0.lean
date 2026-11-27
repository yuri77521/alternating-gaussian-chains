import Point22AtlasRangeGroup111

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf112
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .second

theorem s32_32 : Run get 32 32 ⟨-4399709499682,-4398874390481⟩ :=
  of_check (by decide +kernel)

theorem s64_64 : Run get 64 64 ⟨-4398838379267,-4395427130059⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨-4395354855718,-4381580659430⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨-4381436081393,-4326292878068⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨-4326005468812,-4234911626173⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨-4234485410630,-4108713621254⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨-4108154540036,-3949451989727⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨-3948767783310,-3759322203874⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨-3758522262720,-3540919755017⟩ :=
  of_check (by decide +kernel)

theorem s1792_128 : Run get 1792 128 ⟨-3540014939339,-3422024689910⟩ :=
  of_check (by decide +kernel)

theorem s1920_64 : Run get 1920 64 ⟨-3421071913093,-3360324526124⟩ :=
  of_check (by decide +kernel)

theorem s1984_32 : Run get 1984 32 ⟨-3359348950088,-3328933544615⟩ :=
  of_check (by decide +kernel)

theorem s2016_4 : Run get 2016 4 ⟨-3327946871356,-3324984791311⟩ :=
  of_check (by decide +kernel)

theorem s2020_1 : Run get 2020 1 ⟨-3323996745213,-3323996745210⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨-3540014939339,-3297190610873⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨-3296193044510,-3031375671339⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨-3030298514741,-2746950566814⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨-2745807774604,-2447562233423⟩ :=
  of_check (by decide +kernel)

theorem s2816_128 : Run get 2816 128 ⟨-2446368302261,-2293427339777⟩ :=
  of_check (by decide +kernel)

theorem s2944_64 : Run get 2944 64 ⟨-2292213374756,-2215456933103⟩ :=
  of_check (by decide +kernel)

theorem s3008_4 : Run get 3008 4 ⟨-2214234342828,-2210565808472⟩ :=
  of_check (by decide +kernel)

theorem s3012_2 : Run get 3012 2 ⟨-2209342709940,-2208119484904⟩ :=
  of_check (by decide +kernel)

theorem s3014_1 : Run get 3014 1 ⟨-2206896133603,-2206896133600⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨-2446368302261,-2136963748034⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨-2135733460607,-1818948912240⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨-1817697083168,-1497288039446⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨-1496029268644,-1175666324940⟩ :=
  of_check (by decide +kernel)

theorem s3840_128 : Run get 3840 128 ⟨-1174414763645,-1015984184835⟩ :=
  of_check (by decide +kernel)

theorem s3968_32 : Run get 3968 32 ⟨-1014741335006,-976254195803⟩ :=
  of_check (by decide +kernel)

theorem s4000_8 : Run get 4000 8 ⟨-975014039417,-966335404327⟩ :=
  of_check (by decide +kernel)

theorem s4008_1 : Run get 4008 1 ⟨-965095953070,-965095953067⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨-1174414763645,-857626068877⟩ :=
  of_check (by decide +kernel)

theorem s2048_4 : Run get 2048 4 ⟨-3296193044510,-3293198323612⟩ :=
  of_check (by decide +kernel)

theorem s2052_1 : Run get 2052 1 ⟨-3292199410055,-3292199410052⟩ :=
  of_check (by decide +kernel)

theorem s3968_64 : Run get 3968 64 ⟨-1014741335006,-936613546183⟩ :=
  of_check (by decide +kernel)

theorem s4032_8 : Run get 4032 8 ⟨-935376286120,-926718101929⟩ :=
  of_check (by decide +kernel)

theorem s4040_1 : Run get 4040 1 ⟨-925481597442,-925481597439⟩ :=
  of_check (by decide +kernel)

theorem s96_32 : Run get 96 32 ⟨-4397386724837,-4395427130059⟩ :=
  of_check (by decide +kernel)

theorem s2048_32 : Run get 2048 32 ⟨-3296193044510,-3265102285165⟩ :=
  of_check (by decide +kernel)

theorem s2080_4 : Run get 2080 4 ⟨-3264094031642,-3261067288058⟩ :=
  of_check (by decide +kernel)

theorem s2084_1 : Run get 2084 1 ⟨-3260057713210,-3260057713207⟩ :=
  of_check (by decide +kernel)

theorem s4032_32 : Run get 4032 32 ⟨-935376286120,-897068701091⟩ :=
  of_check (by decide +kernel)

theorem s4064_8 : Run get 4064 8 ⟨-895834538478,-887198211521⟩ :=
  of_check (by decide +kernel)

theorem s4072_1 : Run get 4072 1 ⟨-885964854487,-885964854484⟩ :=
  of_check (by decide +kernel)

theorem s160_32 : Run get 160 32 ⟨-4392743218825,-4389660862418⟩ :=
  of_check (by decide +kernel)

theorem s192_64 : Run get 192 64 ⟨-4389552388531,-4381580659430⟩ :=
  of_check (by decide +kernel)

theorem s1026_2 : Run get 1026 2 ⟨-4107034862842,-4106474267104⟩ :=
  of_check (by decide +kernel)

theorem s1028_4 : Run get 1028 4 ⟨-4105913166771,-4104226839341⟩ :=
  of_check (by decide +kernel)

theorem s1032_8 : Run get 1032 8 ⟨-4103663721792,-4099707793432⟩ :=
  of_check (by decide +kernel)

theorem s1040_16 : Run get 1040 16 ⟨-4099140647177,-4090573154758⟩ :=
  of_check (by decide +kernel)

theorem s1056_32 : Run get 1056 32 ⟨-4089997974173,-4071919429395⟩ :=
  of_check (by decide +kernel)

theorem s1088_64 : Run get 1088 64 ⟨-4071328273946,-4033088451250⟩ :=
  of_check (by decide +kernel)

theorem s1152_128 : Run get 1152 128 ⟨-4032465732861,-3949451989727⟩ :=
  of_check (by decide +kernel)

theorem s2020_4 : Run get 2020 4 ⟨-3323996745213,-3321030551440⟩ :=
  of_check (by decide +kernel)

theorem s2024_8 : Run get 2024 8 ⟨-3320041135697,-3313105663125⟩ :=
  of_check (by decide +kernel)

theorem s2032_16 : Run get 2032 16 ⟨-3312113517684,-3297190610873⟩ :=
  of_check (by decide +kernel)

theorem s2052_4 : Run get 2052 4 ⟨-3292199410055,-3289200652406⟩ :=
  of_check (by decide +kernel)

theorem s2056_8 : Run get 2056 8 ⟨-3288200394876,-3281189209732⟩ :=
  of_check (by decide +kernel)

theorem s2064_16 : Run get 2064 16 ⟨-3280186273935,-3265102285165⟩ :=
  of_check (by decide +kernel)

theorem s2080_32 : Run get 2080 32 ⟨-3264094031642,-3232675185195⟩ :=
  of_check (by decide +kernel)

theorem s2112_64 : Run get 2112 64 ⟨-3231656452220,-3166831409014⟩ :=
  of_check (by decide +kernel)

theorem s2176_128 : Run get 2176 128 ⟨-3165792347017,-3031375671339⟩ :=
  of_check (by decide +kernel)

theorem s2084_4 : Run get 2084 4 ⟨-3260057713210,-3257027010520⟩ :=
  of_check (by decide +kernel)

theorem s2088_8 : Run get 2088 8 ⟨-3256016117594,-3248930666164⟩ :=
  of_check (by decide +kernel)

theorem s2096_16 : Run get 2096 16 ⟨-3247917146844,-3232675185195⟩ :=
  of_check (by decide +kernel)

theorem s2116_4 : Run get 2116 4 ⟨-3227578281183,-3224516257550⟩ :=
  of_check (by decide +kernel)

theorem s2120_8 : Run get 2120 8 ⟨-3223494937368,-3216336678130⟩ :=
  of_check (by decide +kernel)

theorem s2128_16 : Run get 2128 16 ⟨-3215312783855,-3199915984196⟩ :=
  of_check (by decide +kernel)

theorem s2144_32 : Run get 2144 32 ⟨-3198886981182,-3166831409014⟩ :=
  of_check (by decide +kernel)

theorem s3014_2 : Run get 3014 2 ⟨-2206896133603,-2205672656251⟩ :=
  of_check (by decide +kernel)

theorem s3016_8 : Run get 3016 8 ⟨-2204449053087,-2195880327046⟩ :=
  of_check (by decide +kernel)

theorem s3024_16 : Run get 3024 16 ⟨-2194655725495,-2176271975603⟩ :=
  of_check (by decide +kernel)

theorem s3040_32 : Run get 3040 32 ⟨-2175045420778,-2136963748034⟩ :=
  of_check (by decide +kernel)

theorem s4008_8 : Run get 4008 8 ⟨-965095953070,-956422298183⟩ :=
  of_check (by decide +kernel)

theorem s4016_16 : Run get 4016 16 ⟨-955183564706,-936613546183⟩ :=
  of_check (by decide +kernel)

theorem s4032_64 : Run get 4032 64 ⟨-935376286120,-857626068877⟩ :=
  of_check (by decide +kernel)

theorem s4040_8 : Run get 4040 8 ⟨-925481597442,-916828746203⟩ :=
  of_check (by decide +kernel)

theorem s4048_16 : Run get 4048 16 ⟨-915593009835,-897068701091⟩ :=
  of_check (by decide +kernel)

theorem s4064_32 : Run get 4064 32 ⟨-895834538478,-857626068877⟩ :=
  of_check (by decide +kernel)

theorem s4072_8 : Run get 4072 8 ⟨-885964854487,-877334210108⟩ :=
  of_check (by decide +kernel)

theorem s4080_16 : Run get 4080 16 ⟨-876101671083,-857626068877⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf112
