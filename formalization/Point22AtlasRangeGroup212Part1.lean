import Point22AtlasRangeGroup212Part0

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf212
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 2 1 .second

theorem s4096_8 : Run get 4096 8 ⟨39416084470,39439335436⟩ :=
  of_check (by decide +kernel)

theorem s4104_1 : Run get 4104 1 ⟨39412738142,39412738148⟩ :=
  of_check (by decide +kernel)

theorem s4096_256 : Run get 4096 256 ⟨38401481434,39439335436⟩ :=
  of_check (by decide +kernel)

theorem s4352_256 : Run get 4352 256 ⟨36987026160,38396659598⟩ :=
  of_check (by decide +kernel)

theorem s4608_256 : Run get 4608 256 ⟨35236550716,36980816494⟩ :=
  of_check (by decide +kernel)

theorem s4864_256 : Run get 4864 256 ⟨33191030950,35229106726⟩ :=
  of_check (by decide +kernel)

theorem s5120_256 : Run get 5120 256 ⟨30894163499,33182518671⟩ :=
  of_check (by decide +kernel)

theorem s5376_256 : Run get 5376 256 ⟨28391386078,30884757669⟩ :=
  of_check (by decide +kernel)

theorem s5632_256 : Run get 5632 256 ⟨25728913385,28381266329⟩ :=
  of_check (by decide +kernel)

theorem s5888_128 : Run get 5888 128 ⟨24352216935,25718260540⟩ :=
  of_check (by decide +kernel)

theorem s6016_8 : Run get 6016 8 ⟨24265360865,24341364754⟩ :=
  of_check (by decide +kernel)

theorem s6024_4 : Run get 6024 4 ⟨24221900006,24254497696⟩ :=
  of_check (by decide +kernel)

theorem s6028_1 : Run get 6028 1 ⟨24211031401,24211031407⟩ :=
  of_check (by decide +kernel)

theorem s5888_256 : Run get 5888 256 ⟨22952811443,25718260540⟩ :=
  of_check (by decide +kernel)

theorem s6144_256 : Run get 6144 256 ⟨20108130868,22941803998⟩ :=
  of_check (by decide +kernel)

theorem s6400_256 : Run get 6400 256 ⟨17238116711,20096941745⟩ :=
  of_check (by decide +kernel)

theorem s6656_256 : Run get 6656 256 ⟨14383509394,17226910351⟩ :=
  of_check (by decide +kernel)

theorem s6912_256 : Run get 6912 256 ⟨11581947796,14372439210⟩ :=
  of_check (by decide +kernel)

theorem s7168_256 : Run get 7168 256 ⟨8867482087,11571154060⟩ :=
  of_check (by decide +kernel)

theorem s7424_256 : Run get 7424 256 ⟨6270200387,8857090243⟩ :=
  of_check (by decide +kernel)

theorem s7680_256 : Run get 7680 256 ⟨3815969985,6260319822⟩ :=
  of_check (by decide +kernel)

theorem s7936_64 : Run get 7936 64 ⟨3227380620,3806693240⟩ :=
  of_check (by decide +kernel)

theorem s8000_16 : Run get 8000 16 ⟨3081878291,3218267275⟩ :=
  of_check (by decide +kernel)

theorem s8016_1 : Run get 8016 1 ⟨3072806493,3072806499⟩ :=
  of_check (by decide +kernel)

theorem s4864_128 : Run get 4864 128 ⟨34247992603,35229106726⟩ :=
  of_check (by decide +kernel)

theorem s4992_64 : Run get 4992 64 ⟨33727718910,34239993080⟩ :=
  of_check (by decide +kernel)

theorem s5056_8 : Run get 5056 8 ⟨33661516356,33719457596⟩ :=
  of_check (by decide +kernel)

theorem s5064_2 : Run get 5064 2 ⟨33644925801,33653223076⟩ :=
  of_check (by decide +kernel)

theorem s5066_1 : Run get 5066 1 ⟨33636624551,33636624557⟩ :=
  of_check (by decide +kernel)

theorem s6016_32 : Run get 6016 32 ⟨24004274348,24341364754⟩ :=
  of_check (by decide +kernel)

theorem s6048_8 : Run get 6048 8 ⟨23917077322,23993379247⟩ :=
  of_check (by decide +kernel)

theorem s6056_4 : Run get 6056 4 ⟨23873448046,23906171920⟩ :=
  of_check (by decide +kernel)

theorem s6060_1 : Run get 6060 1 ⟨23862537552,23862537558⟩ :=
  of_check (by decide +kernel)

theorem s8000_32 : Run get 8000 32 ⟨2937042881,3218267275⟩ :=
  of_check (by decide +kernel)

theorem s8032_16 : Run get 8032 16 ⟨2792878729,2928012916⟩ :=
  of_check (by decide +kernel)

theorem s8048_1 : Run get 8048 1 ⟨2783890855,2783890861⟩ :=
  of_check (by decide +kernel)

theorem s4104_8 : Run get 4104 8 ⟨39389140756,39412738148⟩ :=
  of_check (by decide +kernel)

theorem s4112_16 : Run get 4112 16 ⟨39334069121,39385745003⟩ :=
  of_check (by decide +kernel)

theorem s4128_32 : Run get 4128 32 ⟨39219215304,39330574853⟩ :=
  of_check (by decide +kernel)

theorem s4160_64 : Run get 4160 64 ⟨38970880008,39215525424⟩ :=
  of_check (by decide +kernel)

theorem s4224_128 : Run get 4224 128 ⟨38401481434,38966804707⟩ :=
  of_check (by decide +kernel)

theorem s6016_64 : Run get 6016 64 ⟨23655000885,24341364754⟩ :=
  of_check (by decide +kernel)

theorem s6080_8 : Run get 6080 8 ⟨23567484848,23644065608⟩ :=
  of_check (by decide +kernel)

theorem s6088_4 : Run get 6088 4 ⟨23523698118,23556539953⟩ :=
  of_check (by decide +kernel)

theorem s6092_1 : Run get 6092 1 ⟨23512748473,23512748479⟩ :=
  of_check (by decide +kernel)

theorem s7936_128 : Run get 7936 128 ⟨2649390107,3806693240⟩ :=
  of_check (by decide +kernel)

theorem s8064_16 : Run get 8064 16 ⟨2506581221,2640444601⟩ :=
  of_check (by decide +kernel)

theorem s8080_1 : Run get 8080 1 ⟨2497678331,2497678337⟩ :=
  of_check (by decide +kernel)

theorem s6028_4 : Run get 6028 4 ⟨24178417493,24211031407⟩ :=
  of_check (by decide +kernel)

theorem s6032_16 : Run get 6032 16 ⟨24004274348,24167543508⟩ :=
  of_check (by decide +kernel)

theorem s6048_32 : Run get 6048 32 ⟨23655000885,23993379247⟩ :=
  of_check (by decide +kernel)

theorem s6080_64 : Run get 6080 64 ⟨22952811443,23644065608⟩ :=
  of_check (by decide +kernel)

theorem s6060_4 : Run get 6060 4 ⟨23829798490,23862537558⟩ :=
  of_check (by decide +kernel)

theorem s6064_16 : Run get 6064 16 ⟨23655000885,23818882958⟩ :=
  of_check (by decide +kernel)

theorem s6092_4 : Run get 6092 4 ⟨23479892474,23512748479⟩ :=
  of_check (by decide +kernel)

theorem s6096_16 : Run get 6096 16 ⟨23304484174,23468938134⟩ :=
  of_check (by decide +kernel)

theorem s6112_32 : Run get 6112 32 ⟨22952811443,23293511452⟩ :=
  of_check (by decide +kernel)

theorem s8016_16 : Run get 8016 16 ⟨2937042881,3072806499⟩ :=
  of_check (by decide +kernel)

theorem s8032_32 : Run get 8032 32 ⟨2649390107,2928012916⟩ :=
  of_check (by decide +kernel)

theorem s8064_128 : Run get 8064 128 ⟨1526290712,2640444601⟩ :=
  of_check (by decide +kernel)

theorem s8048_16 : Run get 8048 16 ⟨2649390107,2783890861⟩ :=
  of_check (by decide +kernel)

theorem s8080_16 : Run get 8080 16 ⟨2364456209,2497678337⟩ :=
  of_check (by decide +kernel)

theorem s8096_32 : Run get 8096 32 ⟨2082274015,2355596201⟩ :=
  of_check (by decide +kernel)

theorem s8128_64 : Run get 8128 64 ⟨1526290712,2073500517⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf212
