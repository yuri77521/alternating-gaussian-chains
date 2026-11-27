import Point22AtlasRangeGroup210

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf211
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .first

theorem s64_64 : Run get 64 64 ⟨-4399322330,-4396482335⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨-4396419128,-4383793234⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨-4383657678,-4330792827⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨-4330514255,-4241635922⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨-4241218237,-4117568518⟩ :=
  of_check (by decide +kernel)

theorem s1024_32 : Run get 1024 32 ⟨-4117017542,-4099686322⟩ :=
  of_check (by decide +kernel)

theorem s1056_2 : Run get 1056 2 ⟨-4099119187,-4098551537⟩ :=
  of_check (by decide +kernel)

theorem s1058_1 : Run get 1058 1 ⟨-4097983395,-4097983389⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨-4117017542,-3960314850⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨-3959638217,-3772043877⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨-3771250877,-3555327438⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨-3554428847,-3313091132⟩ :=
  of_check (by decide +kernel)

theorem s2048_4 : Run get 2048 4 ⟨-3312099001,-3309120543⟩ :=
  of_check (by decide +kernel)

theorem s2052_1 : Run get 2052 1 ⟨-3308127052,-3308127046⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨-3312099001,-3048559109⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨-3047486540,-2765194120⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨-2764055025,-2466634250⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨-2465443099,-2156627822⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨-2155399388,-1838967950⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨-1837717052,-1517428214⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨-1516169472,-1195700830⟩ :=
  of_check (by decide +kernel)

theorem s3840_128 : Run get 3840 128 ⟨-1194448430,-1035883957⟩ :=
  of_check (by decide +kernel)

theorem s3968_64 : Run get 3968 64 ⟨-1034639852,-956426153⟩ :=
  of_check (by decide +kernel)

theorem s4032_8 : Run get 4032 8 ⟨-955187434,-946518900⟩ :=
  of_check (by decide +kernel)

theorem s4040_1 : Run get 4040 1 ⟨-945280912,-945280906⟩ :=
  of_check (by decide +kernel)

theorem s1058_2 : Run get 1058 2 ⟨-4097983395,-4097414740⟩ :=
  of_check (by decide +kernel)

theorem s1060_4 : Run get 1060 4 ⟨-4096845593,-4095135115⟩ :=
  of_check (by decide +kernel)

theorem s1064_8 : Run get 1064 8 ⟨-4094563958,-4090551766⟩ :=
  of_check (by decide +kernel)

theorem s1072_16 : Run get 1072 16 ⟨-4089976596,-4081288894⟩ :=
  of_check (by decide +kernel)

theorem s1088_64 : Run get 1088 64 ⟨-4080705722,-4042964378⟩ :=
  of_check (by decide +kernel)

theorem s1152_128 : Run get 1152 128 ⟨-4042349513,-3960314850⟩ :=
  of_check (by decide +kernel)

theorem s2052_4 : Run get 2052 4 ⟨-3308127052,-3305144519⟩ :=
  of_check (by decide +kernel)

theorem s2056_8 : Run get 2056 8 ⟨-3304149671,-3297176216⟩ :=
  of_check (by decide +kernel)

theorem s2064_16 : Run get 2064 16 ⟨-3296178665,-3281174953⟩ :=
  of_check (by decide +kernel)

theorem s2080_32 : Run get 2080 32 ⟨-3280172031,-3248916686⟩ :=
  of_check (by decide +kernel)

theorem s2112_64 : Run get 2112 64 ⟨-3247903182,-3183400527⟩ :=
  of_check (by decide +kernel)

theorem s2176_128 : Run get 2176 128 ⟨-3182366482,-3048559109⟩ :=
  of_check (by decide +kernel)

theorem s2084_4 : Run get 2084 4 ⟨-3276156986,-3273142198⟩ :=
  of_check (by decide +kernel)

theorem s2088_8 : Run get 2088 8 ⟨-3272136612,-3265088166⟩ :=
  of_check (by decide +kernel)

theorem s2096_16 : Run get 2096 16 ⟨-3264079927,-3248916686⟩ :=
  of_check (by decide +kernel)

theorem s4032_32 : Run get 4032 32 ⟨-955187434,-916832869⟩ :=
  of_check (by decide +kernel)

theorem s4064_8 : Run get 4064 8 ⟨-915597147,-906949769⟩ :=
  of_check (by decide +kernel)

theorem s4072_1 : Run get 4072 1 ⟨-905714828,-905714822⟩ :=
  of_check (by decide +kernel)

theorem s2116_4 : Run get 2116 4 ⟨-3243845868,-3240799446⟩ :=
  of_check (by decide +kernel)

theorem s2120_8 : Run get 2120 8 ⟨-3239783328,-3232661345⟩ :=
  of_check (by decide +kernel)

theorem s2128_16 : Run get 2128 16 ⟨-3231642627,-3216322977⟩ :=
  of_check (by decide +kernel)

theorem s2144_32 : Run get 2144 32 ⟨-3215299098,-3183400527⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨-1194448430,-877338599⟩ :=
  of_check (by decide +kernel)

theorem s3046_2 : Run get 3046 2 ⟨-2187300305,-2186074845⟩ :=
  of_check (by decide +kernel)

theorem s3048_8 : Run get 3048 8 ⟨-2184849275,-2176266837⟩ :=
  of_check (by decide +kernel)

theorem s3056_16 : Run get 3056 16 ⟨-2175040298,-2156627822⟩ :=
  of_check (by decide +kernel)

theorem s4040_8 : Run get 4040 8 ⟨-945280912,-936617535⟩ :=
  of_check (by decide +kernel)

theorem s4048_16 : Run get 4048 16 ⟨-935380290,-916832869⟩ :=
  of_check (by decide +kernel)

theorem s4064_32 : Run get 4064 32 ⟨-915597147,-877338599⟩ :=
  of_check (by decide +kernel)

theorem s4072_8 : Run get 4072 8 ⟨-905714828,-897072957⟩ :=
  of_check (by decide +kernel)

theorem s4080_16 : Run get 4080 16 ⟨-895838809,-877338599⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf211
