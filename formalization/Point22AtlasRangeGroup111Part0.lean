import Point22AtlasRangeGroup110

/-! One bounded segment of the width-22 integer range certificate. -/
namespace GaussianChains.Point22.Atlas.RangeTicks.Leaf111
open Tables GaussianChains.ImageBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

private abbrev get := fastBlock verifiedRow 1 1 .first

theorem s32_32 : Run get 32 32 ⟨-8661761161,-4399903094⟩ :=
  of_check (by decide +kernel)

theorem s64_64 : Run get 64 64 ⟨-17456449498,-8799225421⟩ :=
  of_check (by decide +kernel)

theorem s128_128 : Run get 128 128 ⟨-35013550279,-17593805465⟩ :=
  of_check (by decide +kernel)

theorem s256_256 : Run get 256 256 ⟨-69869427654,-35150472414⟩ :=
  of_check (by decide +kernel)

theorem s512_256 : Run get 512 256 ⟨-104137942404,-70004619814⟩ :=
  of_check (by decide +kernel)

theorem s768_256 : Run get 768 256 ⟨-137535126554,-104270276731⟩ :=
  of_check (by decide +kernel)

theorem s1024_256 : Run get 1024 256 ⟨-169789151266,-137663515117⟩ :=
  of_check (by decide +kernel)

theorem s1280_256 : Run get 1280 256 ⟨-200644007678,-169912560948⟩ :=
  of_check (by decide +kernel)

theorem s1536_256 : Run get 1536 256 ⟨-229862881543,-200761473995⟩ :=
  of_check (by decide +kernel)

theorem s1792_128 : Run get 1792 128 ⟨-243790817390,-229973521145⟩ :=
  of_check (by decide +kernel)

theorem s1920_64 : Run get 1920 64 ⟨-250573409867,-243897740772⟩ :=
  of_check (by decide +kernel)

theorem s1984_32 : Run get 1984 32 ⟨-253918068503,-250678404763⟩ :=
  of_check (by decide +kernel)

theorem s2016_4 : Run get 2016 4 ⟨-254333938457,-254022082258⟩ :=
  of_check (by decide +kernel)

theorem s2020_1 : Run get 2020 1 ⟨-254437828794,-254437828791⟩ :=
  of_check (by decide +kernel)

theorem s1792_256 : Run get 1792 256 ⟨-257231159638,-229973521145⟩ :=
  of_check (by decide +kernel)

theorem s2048_256 : Run get 2048 256 ⟨-282559014963,-257334181256⟩ :=
  of_check (by decide +kernel)

theorem s2304_256 : Run get 2304 256 ⟨-305683528027,-282653728620⟩ :=
  of_check (by decide +kernel)

theorem s2560_256 : Run get 2560 256 ⟨-326470312651,-305769352374⟩ :=
  of_check (by decide +kernel)

theorem s2816_128 : Run get 2816 128 ⟨-335953147202,-326546780313⟩ :=
  of_check (by decide +kernel)

theorem s2944_64 : Run get 2944 64 ⟨-340462123555,-336024797836⟩ :=
  of_check (by decide +kernel)

theorem s3008_4 : Run get 3008 4 ⟨-340738749998,-340531337479⟩ :=
  of_check (by decide +kernel)

theorem s3012_2 : Run get 3012 2 ⟨-340876833916,-340807811066⟩ :=
  of_check (by decide +kernel)

theorem s3014_1 : Run get 3014 1 ⟨-340945818535,-340945818532⟩ :=
  of_check (by decide +kernel)

theorem s2816_256 : Run get 2816 256 ⟨-344814626416,-326546780313⟩ :=
  of_check (by decide +kernel)

theorem s3072_256 : Run get 3072 256 ⟨-360641957801,-344881387308⟩ :=
  of_check (by decide +kernel)

theorem s3328_256 : Run get 3328 256 ⟨-373908093854,-360698780392⟩ :=
  of_check (by decide +kernel)

theorem s3584_256 : Run get 3584 256 ⟨-384598683609,-373954864434⟩ :=
  of_check (by decide +kernel)

theorem s3840_128 : Run get 3840 128 ⟨-388981613421,-384635403623⟩ :=
  of_check (by decide +kernel)

theorem s3968_32 : Run get 3968 32 ⟨-389977725437,-389013343504⟩ :=
  of_check (by decide +kernel)

theorem s4000_8 : Run get 4000 8 ⟨-390220549020,-390008214000⟩ :=
  of_check (by decide +kernel)

theorem s4008_1 : Run get 4008 1 ⟨-390250727634,-390250727631⟩ :=
  of_check (by decide +kernel)

theorem s3840_256 : Run get 3840 256 ⟨-392728323067,-384635403623⟩ :=
  of_check (by decide +kernel)

theorem s2048_4 : Run get 2048 4 ⟨-257643059003,-257334181256⟩ :=
  of_check (by decide +kernel)

theorem s2052_1 : Run get 2052 1 ⟨-257745955843,-257745955840⟩ :=
  of_check (by decide +kernel)

theorem s3968_64 : Run get 3968 64 ⟨-390934151593,-389013343504⟩ :=
  of_check (by decide +kernel)

theorem s4032_8 : Run get 4032 8 ⟨-391167067923,-390963401431⟩ :=
  of_check (by decide +kernel)

theorem s4040_1 : Run get 4040 1 ⟨-391196008543,-391196008540⟩ :=
  of_check (by decide +kernel)

theorem s96_32 : Run get 96 32 ⟨-17456449498,-13197386340⟩ :=
  of_check (by decide +kernel)

theorem s4032_32 : Run get 4032 32 ⟨-391850984465,-390963401431⟩ :=
  of_check (by decide +kernel)

theorem s4064_8 : Run get 4064 8 ⟨-392074017695,-391878998575⟩ :=
  of_check (by decide +kernel)

theorem s4072_1 : Run get 4072 1 ⟨-392101723368,-392101723365⟩ :=
  of_check (by decide +kernel)

theorem s2020_4 : Run get 2020 4 ⟨-254749314473,-254437828791⟩ :=
  of_check (by decide +kernel)

theorem s2024_8 : Run get 2024 8 ⟨-255578581955,-254853081216⟩ :=
  of_check (by decide +kernel)

theorem s2032_16 : Run get 2032 16 ⟨-257231159638,-255682101002⟩ :=
  of_check (by decide +kernel)

theorem s2052_4 : Run get 2052 4 ⟨-258054458995,-257745955840⟩ :=
  of_check (by decide +kernel)

theorem s2056_8 : Run get 2056 8 ⟨-258875758174,-258157230884⟩ :=
  of_check (by decide +kernel)

theorem s2064_16 : Run get 2064 16 ⟨-260512334594,-258978279664⟩ :=
  of_check (by decide +kernel)

theorem s2080_32 : Run get 2080 32 ⟨-263761251283,-260614353284⟩ :=
  of_check (by decide +kernel)

theorem s2112_64 : Run get 2112 64 ⟨-270160974793,-263862256463⟩ :=
  of_check (by decide +kernel)

theorem s2176_128 : Run get 2176 128 ⟨-282559014963,-270259922037⟩ :=
  of_check (by decide +kernel)

theorem s2084_4 : Run get 2084 4 ⟨-261327601196,-261022112823⟩ :=
  of_check (by decide +kernel)

theorem s2088_8 : Run get 2088 8 ⟨-262140846343,-261429367493⟩ :=
  of_check (by decide +kernel)

theorem s2096_16 : Run get 2096 16 ⟨-263761251283,-262242359588⟩ :=
  of_check (by decide +kernel)

theorem s2116_4 : Run get 2116 4 ⟨-264568400645,-264265958688⟩ :=
  of_check (by decide +kernel)

theorem s2120_8 : Run get 2120 8 ⟨-265373507691,-264669150818⟩ :=
  of_check (by decide +kernel)

theorem s2128_16 : Run get 2128 16 ⟨-266977574263,-265474002212⟩ :=
  of_check (by decide +kernel)

theorem s2144_32 : Run get 2144 32 ⟨-270160974793,-267077555558⟩ :=
  of_check (by decide +kernel)

theorem s3014_2 : Run get 3014 2 ⟨-341014764923,-340945818532⟩ :=
  of_check (by decide +kernel)

theorem s3016_8 : Run get 3016 8 ⟨-341564959212,-341083673072⟩ :=
  of_check (by decide +kernel)

theorem s3024_16 : Run get 3024 16 ⟨-342657998591,-341633561335⟩ :=
  of_check (by decide +kernel)

theorem s3040_32 : Run get 3040 32 ⟨-344814626416,-342725987923⟩ :=
  of_check (by decide +kernel)

theorem s4008_8 : Run get 4008 8 ⟨-390460893613,-390250727631⟩ :=
  of_check (by decide +kernel)

theorem s4016_16 : Run get 4016 16 ⟨-390934151593,-390490762451⟩ :=
  of_check (by decide +kernel)

theorem s4032_64 : Run get 4032 64 ⟨-392728323067,-390963401431⟩ :=
  of_check (by decide +kernel)

theorem s4040_8 : Run get 4040 8 ⟨-391397511151,-391196008540⟩ :=
  of_check (by decide +kernel)

theorem s4048_16 : Run get 4048 16 ⟨-391850984465,-391426142738⟩ :=
  of_check (by decide +kernel)

theorem s4064_32 : Run get 4064 32 ⟨-392728323067,-391878998575⟩ :=
  of_check (by decide +kernel)

theorem s4072_8 : Run get 4072 8 ⟨-392294584111,-392101723365⟩ :=
  of_check (by decide +kernel)

theorem s4080_16 : Run get 4080 16 ⟨-392728323067,-392321981544⟩ :=
  of_check (by decide +kernel)

end GaussianChains.Point22.Atlas.RangeTicks.Leaf111
